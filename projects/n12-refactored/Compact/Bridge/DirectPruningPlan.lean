import Compact.Bridge.IndexedRelaxation
import Compact.Core.RelaxationHints
import Compact.Core.EmptyContext
import Compact.Core.RegionDAG

/-! Direct original-pose pruning, without raw-piece pose records.

A blocked conjunction is excluded by a separately proved overlap argument.
Its first false face gives an exhaustive surviving context, retaining every
preceding true face. Each whole context must imply an original final target
or a checked strict Farkas contradiction. No target-hull or vertex-only union
coverage is substituted for this universal implication. Strict complements
are computed as rows, so they need not already have dictionary identifiers.
-/

set_option Elab.async false

namespace N12Compact.DirectPruningPlan
open S12 S12Pilot IntegerSupport IndexedRelaxation

def outsideRows : List Row → List Row → List (List Row)
  | [], _ => []
  | row :: rest, inputs =>
      (RegionDAG.opposite row :: inputs) :: outsideRows rest (row :: inputs)

theorem outsideRows_sound (block inputs : List Row) (p : Fin 2 → ℝ)
    (incoming : ∀ row ∈ inputs, row.Holds p)
    (forbidden : ¬ (∀ row ∈ block, row.Holds p)) :
    ∃ context ∈ outsideRows block inputs, ∀ row ∈ context, row.Holds p := by
  induction block generalizing inputs with
  | nil => exact (forbidden (by simp)).elim
  | cons row rest ih =>
      by_cases holds : row.Holds p
      · have tail_forbidden : ¬ (∀ r ∈ rest, r.Holds p) := by
          intro all
          apply forbidden
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact holds
          · exact all r hr
        obtain ⟨context, member, all⟩ := ih (row :: inputs)
          (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr
              · exact holds
              · exact incoming r hr)
          tail_forbidden
        exact ⟨context, List.mem_cons_of_mem _ member, all⟩
      · refine ⟨RegionDAG.opposite row :: inputs, List.mem_cons_self, ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (RegionDAG.opposite_holds row p).mpr holds
        · exact incoming r hr

inductive Outcome (poseCount : Nat) (inputs : List Row) where
  | keep (target : Fin poseCount) (hints : List RelaxationHints.Hint)
  | close (witness : EmptyContext.Witness inputs.length)

structure Branch (poseCount : Nat) where
  inputs : List Row
  outcome : Outcome poseCount inputs

variable {r m a : Nat}

def Branch.targets (branch : Branch m) : List (Fin m) :=
  match branch.outcome with
  | .keep target _ => [target]
  | .close _ => []

def Branch.Check (branch : Branch m) (d : Dictionary r m a) (source : Fin m) : Prop :=
  match branch.outcome with
  | .keep target hints =>
      d.poseAngle source = d.poseAngle target ∧
      RelaxationHints.Check branch.inputs ((d.poseRows target).map d.rows) hints
  | .close witness => witness.Check (fun i => branch.inputs[i.val])

instance (branch : Branch m) (d : Dictionary r m a) (source : Fin m) :
    Decidable (branch.Check d source) := by
  unfold Branch.Check
  split <;> infer_instance

theorem Branch.sound (branch : Branch m) (d : Dictionary r m a) (source : Fin m)
    (positive : ∀ i, 0 < d.denominators i) (checked : branch.Check d source)
    (q : OpenSquare) (hq : (d.pose source).OrientedRealizes q)
    (holds : ∀ row ∈ branch.inputs, row.Holds ![centerX q, centerY q]) :
    OrientedPoseCovered (branch.targets.map d.pose) q := by
  cases branch with
  | mk inputs outcome =>
      cases outcome with
      | keep target hints =>
          change d.poseAngle source = d.poseAngle target ∧
            RelaxationHints.Check inputs ((d.poseRows target).map d.rows) hints at checked
          refine ⟨d.pose target, by simp [Branch.targets], ?_⟩
          apply d.transfer checked.1 positive q hq
          intro row member
          exact RelaxationHints.sound checked.2 _ holds (d.rows row)
            (List.mem_map.mpr ⟨row, member, rfl⟩)
      | close witness =>
          exfalso
          apply witness.sound (fun i => inputs[i.val]) checked ![centerX q, centerY q]
          intro i _
          exact holds _ (List.getElem_mem i.isLt)

structure Plan (rowCount poseCount : Nat) where
  source : Fin poseCount
  block : Option (List (Fin rowCount))
  branches : List (Branch poseCount)

def Plan.contexts (plan : Plan r m) (d : Dictionary r m a) : List (List Row) :=
  match plan.block with
  | none => [(d.poseRows plan.source).map d.rows]
  | some block => outsideRows (block.map d.rows) ((d.poseRows plan.source).map d.rows)

def Plan.targets (plan : Plan r m) : List (Fin m) :=
  plan.branches.flatMap Branch.targets

def Plan.Check (plan : Plan r m) (d : Dictionary r m a) : Prop :=
  ∀ context ∈ plan.contexts d, ∃ branch ∈ plan.branches,
    branch.inputs = context ∧ branch.Check d plan.source

instance (plan : Plan r m) (d : Dictionary r m a) : Decidable (plan.Check d) := by
  unfold Plan.Check
  letI : DecidablePred (fun context => ∃ branch ∈ plan.branches,
      branch.inputs = context ∧ branch.Check d plan.source) :=
    fun context => List.decidableBEx _ plan.branches
  exact List.decidableBAll _ (plan.contexts d)

theorem Plan.sound (plan : Plan r m) (d : Dictionary r m a)
    (positive : ∀ i, 0 < d.denominators i) (checked : plan.Check d)
    (q : OpenSquare) (hq : (d.pose plan.source).OrientedRealizes q)
    (forbidden : ∀ block, plan.block = some block →
      ¬ (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q])) :
    OrientedPoseCovered (plan.targets.map d.pose) q := by
  have incoming : ∀ row ∈ (d.poseRows plan.source).map d.rows,
      row.Holds ![centerX q, centerY q] := by
    intro row member
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
    apply ((d.rows i).normalized_holds_iff _ (positive i) _).mp
    exact hq.1.1 _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have surviving : ∃ context ∈ plan.contexts d,
      ∀ row ∈ context, row.Holds ![centerX q, centerY q] := by
    cases block_eq : plan.block with
    | none =>
        exact ⟨(d.poseRows plan.source).map d.rows, by simp [Plan.contexts, block_eq], incoming⟩
    | some block =>
        have impossible : ¬ (∀ row ∈ block.map d.rows,
            row.Holds ![centerX q, centerY q]) := by
          intro all
          apply forbidden block block_eq
          intro i hi
          exact all (d.rows i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
        obtain ⟨context, member, all⟩ := outsideRows_sound
          (block.map d.rows) ((d.poseRows plan.source).map d.rows) _ incoming impossible
        exact ⟨context, by simpa only [Plan.contexts, block_eq] using member, all⟩
  obtain ⟨context, member, all⟩ := surviving
  obtain ⟨branch, included, same_inputs, branch_checked⟩ := checked context member
  obtain ⟨pose, pose_member, realizes⟩ := branch.sound d plan.source positive
    branch_checked q hq (by simpa only [same_inputs] using all)
  obtain ⟨target, target_member, rfl⟩ := List.mem_map.mp pose_member
  refine ⟨d.pose target, List.mem_map.mpr ⟨target, ?_, rfl⟩, realizes⟩
  exact List.mem_flatMap.mpr ⟨branch, included, target_member⟩

def CoverCheck (sources targets : List (Fin m)) (plans : List (Plan r m)) : Prop :=
  ∀ source ∈ sources, ∃ plan ∈ plans, plan.source = source ∧
    ∀ target ∈ plan.targets, target ∈ targets

/-! Source coverage is a single list equality.  In particular, a producer need
not search all plans again for every original source pose. -/
theorem cover_of_source_map (sources targets : List (Fin m))
    (plans : List (Plan r m)) (same_sources : plans.map Plan.source = sources)
    (included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ targets) :
    CoverCheck sources targets plans := by
  intro source member
  rw [← same_sources] at member
  obtain ⟨plan, in_plans, same_source⟩ := List.mem_map.mp member
  exact ⟨plan, in_plans, same_source, included plan in_plans⟩

instance (sources targets : List (Fin m)) (plans : List (Plan r m)) :
    Decidable (CoverCheck sources targets plans) := by
  unfold CoverCheck
  letI : DecidablePred (fun source => ∃ plan ∈ plans, plan.source = source ∧
      ∀ target ∈ plan.targets, target ∈ targets) := fun source => by
    letI : DecidablePred (fun plan : Plan r m => plan.source = source ∧
        ∀ target ∈ plan.targets, target ∈ targets) := fun plan => by
      letI : Decidable (∀ target ∈ plan.targets, target ∈ targets) :=
        List.decidableBAll _ plan.targets
      infer_instance
    exact List.decidableBEx _ plans
  exact List.decidableBAll _ sources

theorem cover_sound (d : Dictionary r m a) (positive : ∀ i, 0 < d.denominators i)
    (sources targets : List (Fin m)) (plans : List (Plan r m))
    (covered : CoverCheck sources targets plans) (checked : ∀ plan ∈ plans, plan.Check d)
    (q : OpenSquare) (hq : OrientedPoseCovered (sources.map d.pose) q)
    (forbidden : ∀ plan ∈ plans, (d.pose plan.source).OrientedRealizes q →
      ∀ block, plan.block = some block →
        ¬ (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q])) :
    OrientedPoseCovered (targets.map d.pose) q := by
  obtain ⟨pose, pose_member, realizes⟩ := hq
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp pose_member
  obtain ⟨plan, plan_member, same_source, all_targets⟩ := covered source in_sources
  have incoming : (d.pose plan.source).OrientedRealizes q := by
    simpa only [same_source] using realizes
  obtain ⟨pose, pose_member, output⟩ := plan.sound d positive
    (checked plan plan_member) q incoming (forbidden plan plan_member incoming)
  obtain ⟨target, target_member, rfl⟩ := List.mem_map.mp pose_member
  exact ⟨d.pose target, List.mem_map.mpr ⟨target, all_targets target target_member, rfl⟩, output⟩

#print axioms Plan.sound
#print axioms cover_sound
end N12Compact.DirectPruningPlan
