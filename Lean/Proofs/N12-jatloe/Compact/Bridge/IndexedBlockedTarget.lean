import Compact.Bridge.IndexedRelaxation
import Compact.Core.BlockedTarget

/-! Original-pose pruning with a single unchanged final target.

Every cache is linked to the actual original dictionary. A targetless record
requires the actual empty blocked conjunction; its separately proved overlap
excludes the source. All other records retain the target angle and every target
row, using either direct support or the checked whole-target contrapositive.
-/

set_option Elab.async false

namespace N12Compact.IndexedBlockedTarget
open S12 S12Pilot IntegerSupport IndexedRelaxation

structure Plan (rowCount poseCount : Nat) where
  source : Fin poseCount
  block : Option (List (Fin rowCount))
  target : Option (Fin poseCount)
  inputs : List Row
  blocked : List Row
  outputs : List Row
  hints : List (BlockedTarget.Hint inputs.length)

variable {r m a : Nat}

def Plan.header (plan : Plan r m) : Fin m × Option (List (Fin r)) :=
  (plan.source, plan.block)

def Plan.targets (plan : Plan r m) : List (Fin m) := plan.target.toList

def Plan.Check (plan : Plan r m) (d : Dictionary r m a) : Prop :=
  match plan.target with
  | none => plan.block = some []
  | some target =>
      plan.inputs = (d.poseRows plan.source).map d.rows ∧
      plan.blocked = (plan.block.getD []).map d.rows ∧
      plan.outputs = (d.poseRows target).map d.rows ∧
      d.poseAngle plan.source = d.poseAngle target ∧
      BlockedTarget.Check plan.inputs plan.blocked plan.outputs plan.hints ∧
      (plan.block = none → ∀ hint ∈ plan.hints, hint.Independent)

instance (plan : Plan r m) (d : Dictionary r m a) : Decidable (plan.Check d) := by
  unfold Plan.Check
  split
  · infer_instance
  · letI : Decidable (∀ hint ∈ plan.hints, hint.Independent) :=
      List.decidableBAll _ plan.hints
    infer_instance

theorem Plan.sound (plan : Plan r m) (d : Dictionary r m a)
    (positive : ∀ i, 0 < d.denominators i) (checked : plan.Check d)
    (q : OpenSquare) (realizes : (d.pose plan.source).OrientedRealizes q)
    (forbidden : ∀ block, plan.block = some block →
      ¬ (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q])) :
    OrientedPoseCovered (plan.targets.map d.pose) q := by
  cases target_eq : plan.target with
  | none =>
      have empty : plan.block = some [] := by
        simpa only [Plan.Check, target_eq] using checked
      exact (forbidden [] empty (by simp)).elim
  | some target =>
      obtain ⟨inputs, blocked, outputs, angle, rules, independent⟩ :
          plan.inputs = (d.poseRows plan.source).map d.rows ∧
          plan.blocked = (plan.block.getD []).map d.rows ∧
          plan.outputs = (d.poseRows target).map d.rows ∧
          d.poseAngle plan.source = d.poseAngle target ∧
          BlockedTarget.Check plan.inputs plan.blocked plan.outputs plan.hints ∧
          (plan.block = none → ∀ hint ∈ plan.hints, hint.Independent) := by
        simpa only [Plan.Check, target_eq] using checked
      have incoming : ∀ row ∈ plan.inputs, row.Holds ![centerX q, centerY q] := by
        intro row member
        rw [inputs] at member
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
        apply ((d.rows i).normalized_holds_iff _ (positive i) _).mp
        exact realizes.1.1 _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have outgoing : ∀ row ∈ plan.outputs, row.Holds ![centerX q, centerY q] := by
        cases block_eq : plan.block with
        | none => exact BlockedTarget.source_sound rules (independent block_eq) _ incoming
        | some block =>
            apply BlockedTarget.sound rules _ incoming
            intro all
            apply forbidden block block_eq
            intro i hi
            apply all (d.rows i)
            rw [blocked, block_eq]
            exact List.mem_map.mpr ⟨i, hi, rfl⟩
      refine ⟨d.pose target, by simp [Plan.targets, target_eq], ?_⟩
      apply d.transfer angle positive q realizes
      intro i hi
      apply outgoing (d.rows i)
      rw [outputs]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩

def TargetsIn (plans : List (Plan r m)) (targets : List (Fin m)) : Prop :=
  ∀ n ∈ (plans.flatMap Plan.targets).map Fin.val, n ∈ targets.map Fin.val

instance (plans : List (Plan r m)) (targets : List (Fin m)) :
    Decidable (TargetsIn plans targets) :=
  List.decidableBAll _ ((plans.flatMap Plan.targets).map Fin.val)

theorem target_members_of_values (plans : List (Plan r m)) (targets : List (Fin m))
    (included : TargetsIn plans targets) :
    ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ targets := by
  intro plan member target in_plan
  have original : target.val ∈ (plans.flatMap Plan.targets).map Fin.val :=
    List.mem_map.mpr ⟨target, List.mem_flatMap.mpr ⟨plan, member, in_plan⟩, rfl⟩
  obtain ⟨other, other_member, same⟩ := List.mem_map.mp (included _ original)
  have equality : other = target := Fin.ext same
  simpa only [equality] using other_member

structure Stage (d : Dictionary r m a) where
  sources : List (Fin m)
  neighbors : List (Fin m)
  targets : List (Fin m)
  plans : List (Plan r m)

def Stage.headers {d : Dictionary r m a} (stage : Stage d) :=
  stage.plans.map Plan.header

def Stage.Check {d : Dictionary r m a} (stage : Stage d) : Prop :=
  stage.plans.map Plan.source = stage.sources ∧
  TargetsIn stage.plans stage.targets ∧
  ∀ plan ∈ stage.plans, plan.Check d

instance {d : Dictionary r m a} (stage : Stage d) : Decidable stage.Check := by
  unfold Stage.Check
  letI : Decidable (∀ plan ∈ stage.plans, plan.Check d) :=
    List.decidableBAll _ stage.plans
  infer_instance

def Stage.BlockOverlap {d : Dictionary r m a} (stage : Stage d) : Prop :=
  ∀ header ∈ stage.headers, ∀ q t : OpenSquare,
    (d.pose header.1).OrientedRealizes q →
    OrientedPoseCovered (stage.neighbors.map d.pose) t →
    ∀ block, header.2 = some block →
      (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q]) →
      ∃ x y, q.Inside x y ∧ t.Inside x y

theorem Stage.step_sound {d : Dictionary r m a} (stage : Stage d)
    (positive : ∀ i, 0 < d.denominators i) (checked : stage.Check)
    (overlap : stage.BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered (stage.sources.map d.pose) q)
    (neighbors : OrientedPoseCovered (stage.neighbors.map d.pose) t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered (stage.targets.map d.pose) q := by
  obtain ⟨pose, member, realizes⟩ := incoming
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member
  rw [← checked.1] at in_sources
  obtain ⟨plan, in_plans, source_eq⟩ := List.mem_map.mp in_sources
  have hq : (d.pose plan.source).OrientedRealizes q := by
    simpa only [source_eq] using realizes
  obtain ⟨pose, in_output, output⟩ := plan.sound d positive
    (checked.2.2 plan in_plans) q hq (by
      intro block block_eq holds
      have header_member : plan.header ∈ stage.headers :=
        List.mem_map.mpr ⟨plan, in_plans, rfl⟩
      obtain ⟨x, y, inside⟩ := overlap plan.header header_member q t hq neighbors block block_eq holds
      exact disjoint x y inside)
  obtain ⟨target, target_member, rfl⟩ := List.mem_map.mp in_output
  exact ⟨d.pose target, List.mem_map.mpr ⟨target,
    target_members_of_values stage.plans stage.targets checked.2.1 plan in_plans target target_member,
    rfl⟩, output⟩

#print axioms Plan.sound
#print axioms Stage.step_sound
end N12Compact.IndexedBlockedTarget
