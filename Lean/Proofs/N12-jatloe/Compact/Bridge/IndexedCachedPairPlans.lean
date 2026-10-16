import Compact.Core.CachedSupportFan
import Compact.Bridge.IndexedRelaxation

/-!
Cached support fans and pruning plans over an arbitrary checked pose dictionary.
Every neighbor pose remains in the geometric quantifier. Exact row lists,
strict complements and original inner-square references connect cached integer
checks to the unchanged oriented `PoseLeaf` model.
-/

set_option Elab.async false

namespace N12Compact.IndexedCachedPairPlans
open S12 S12Pilot IntegerSupport PairPruning IndexedRelaxation

variable {r m a : Nat}

structure PoseContext (d : Dictionary r m a) where
  pose : Fin m
  block : List (Fin r)
  keyAngle : Nat
  context : CachedSupportFan.Context d.rows
  inputs_exact : context.inputs = block ++ d.poseRows pose
  reference_valid : context.reference.Valid
  reference_exact : context.reference.value = (d.pose pose).angle.val.reference 1

variable {d : Dictionary r m a}

def PoseContext.PairCheck (x y : PoseContext d)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat) : Prop :=
  CachedSupportFan.PairCheck x.context y.context (keys x.keyAngle y.keyAngle) opposite

instance (x y : PoseContext d) (keys : Nat → Nat → Fin 8 → Nat)
    (opposite : Nat → Nat) : Decidable (x.PairCheck y keys opposite) :=
  inferInstanceAs (Decidable (CachedSupportFan.PairCheck _ _ _ _))

theorem PoseContext.pair_sound (x y : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : x.PairCheck y keys opposite)
    (q t : OpenSquare) (hq : (d.pose x.pose).Realizes q)
    (ht : (d.pose y.pose).Realizes t)
    (hxBlock : ∀ i ∈ x.block, (d.rows i).Holds ![centerX q, centerY q])
    (hyBlock : ∀ i ∈ y.block, (d.rows i).Holds ![centerX t, centerY t]) :
    ∃ u v, q.Inside u v ∧ t.Inside u v := by
  have hxc : x.context.reference.value.Check := by
    rw [x.reference_exact]
    exact (d.pose x.pose).angle.val.reference_checked
      (d.pose x.pose).angle.property 1 (by norm_num)
  have hyc : y.context.reference.value.Check := by
    rw [y.reference_exact]
    exact (d.pose y.pose).angle.val.reference_checked
      (d.pose y.pose).angle.property 1 (by norm_num)
  have hx : ∀ i ∈ d.poseRows x.pose, (d.rows i).Holds ![centerX q, centerY q] :=
    inputs_hold d.rows d.denominators positive (d.poseRows x.pose) _ hq.1
  have hy : ∀ i ∈ d.poseRows y.pose, (d.rows i).Holds ![centerX t, centerY t] :=
    inputs_hold d.rows d.denominators positive (d.poseRows y.pose) _ ht.1
  have overlap := CachedSupportFan.pair_sound x.context y.context
    x.reference_valid y.reference_valid hxc hyc (keys x.keyAngle y.keyAngle) opposite
    checked ![centerX q, centerY q] ![centerX t, centerY t]
    (by rw [x.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (hxBlock i) (hx i))
    (by rw [y.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (hyBlock i) (hy i))
  obtain ⟨P, hPq, hPt⟩ := overlap
  refine ⟨P.1, P.2, hq.2 P ?_, ht.2 P ?_⟩
  · simpa only [x.reference_exact, Matrix.cons_val_zero, Matrix.cons_val_one] using hPq
  · simpa only [y.reference_exact, Matrix.cons_val_zero, Matrix.cons_val_one] using hPt

structure Plan (m : Nat) where
  source : Fin m
  block : Option Nat
  pieces : List (Fin m)

def Plan.contexts (plan : Plan m) (d : Dictionary r m a)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r) : List (List (Fin r)) :=
  match plan.block with
  | none => [d.poseRows plan.source]
  | some block => outsidePieces complement (blockRows block) (d.poseRows plan.source)

def Plan.Check (plan : Plan m) (d : Dictionary r m a)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r) : Prop :=
  (∀ context ∈ plan.contexts d blockRows complement, ∃ piece ∈ plan.pieces,
    d.poseRows piece = context ∧ d.poseAngle plan.source = d.poseAngle piece) ∧
  match plan.block with
  | none => True
  | some block => ∀ i ∈ blockRows block, d.rows (complement i) = RegionDAG.opposite (d.rows i)

instance (plan : Plan m) (d : Dictionary r m a)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r) :
    Decidable (plan.Check d blockRows complement) := by
  unfold Plan.Check
  letI : DecidablePred (fun context => ∃ piece ∈ plan.pieces,
      d.poseRows piece = context ∧ d.poseAngle plan.source = d.poseAngle piece) := fun context =>
    List.decidableBEx (fun piece =>
      d.poseRows piece = context ∧ d.poseAngle plan.source = d.poseAngle piece) plan.pieces
  letI : Decidable (∀ context ∈ plan.contexts d blockRows complement, ∃ piece ∈ plan.pieces,
      d.poseRows piece = context ∧ d.poseAngle plan.source = d.poseAngle piece) :=
    List.decidableBAll _ (plan.contexts d blockRows complement)
  cases plan.block with
  | none => infer_instance
  | some block =>
      letI : Decidable (∀ i ∈ blockRows block,
          d.rows (complement i) = RegionDAG.opposite (d.rows i)) :=
        List.decidableBAll _ (blockRows block)
      infer_instance

theorem PoseContext.block_forbidden {n : Nat} (source : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (neighbors : Fin n → PoseContext d) (domain : List (Fin m))
    (complete : ∀ pose ∈ domain, ∃ j, (neighbors j).pose = pose)
    (unblocked : ∀ j, (neighbors j).block = [])
    (checked : ∀ j, source.PairCheck (neighbors j) keys opposite)
    (q t : OpenSquare) (hq : (d.pose source.pose).Realizes q)
    (ht : OrientedPoseCovered (domain.map d.pose) t)
    (disjoint : ∀ u v, ¬(q.Inside u v ∧ t.Inside u v)) :
    ¬(∀ i ∈ source.block, (d.rows i).Holds ![centerX q, centerY q]) := by
  intro holds
  obtain ⟨neighbor, member, realizes⟩ := ht
  obtain ⟨neighbor, in_domain, rfl⟩ := List.mem_map.mp member
  obtain ⟨j, hj⟩ := complete neighbor in_domain
  obtain ⟨u, v, overlap⟩ := source.pair_sound (neighbors j) positive keys opposite
    (checked j) q t hq (by simpa only [hj] using realizes.1) holds
    (by intro i hi; simp [unblocked j] at hi)
  exact disjoint u v overlap

theorem Plan.sound (plan : Plan m) (d : Dictionary r m a)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r)
    (positive : ∀ i, 0 < d.denominators i)
    (checked : plan.Check d blockRows complement) (q : OpenSquare)
    (hq : (d.pose plan.source).OrientedRealizes q)
    (forbidden : ∀ block, plan.block = some block →
      ¬(∀ i ∈ blockRows block, (d.rows i).Holds ![centerX q, centerY q])) :
    OrientedPoseCovered (plan.pieces.map d.pose) q := by
  have incoming : ∀ i ∈ d.poseRows plan.source,
      (d.rows i).Holds ![centerX q, centerY q] :=
    inputs_hold d.rows d.denominators positive (d.poseRows plan.source) _ hq.1.1
  have surviving : ∃ context ∈ plan.contexts d blockRows complement,
      ∀ i ∈ context, (d.rows i).Holds ![centerX q, centerY q] := by
    cases hblock : plan.block with
    | none => exact ⟨d.poseRows plan.source, by simp [Plan.contexts, hblock], incoming⟩
    | some block =>
        have hc := checked.2
        rw [hblock] at hc
        obtain ⟨context, member, holds⟩ := outsidePieces_sound d.rows complement
          (blockRows block) (d.poseRows plan.source) hc _ incoming (forbidden block hblock)
        exact ⟨context, by simpa only [Plan.contexts, hblock] using member, holds⟩
  obtain ⟨context, member, holds⟩ := surviving
  obtain ⟨piece, hpiece, hrows, hangle⟩ := checked.1 context member
  refine ⟨d.pose piece, List.mem_map.mpr ⟨piece, hpiece, rfl⟩, ?_⟩
  apply d.transfer hangle positive q hq
  simpa only [hrows] using holds

def StepCover (sources pieces : List (Fin m)) (plans : List (Plan m)) : Prop :=
  ∀ source ∈ sources, ∃ plan ∈ plans, plan.source = source ∧
    ∀ piece ∈ plan.pieces, piece ∈ pieces

instance (sources pieces : List (Fin m)) (plans : List (Plan m)) :
    Decidable (StepCover sources pieces plans) := by
  unfold StepCover
  letI : DecidablePred (fun source => ∃ plan ∈ plans, plan.source = source ∧
      ∀ piece ∈ plan.pieces, piece ∈ pieces) := fun source => by
    letI : DecidablePred (fun plan : Plan m => plan.source = source ∧
        ∀ piece ∈ plan.pieces, piece ∈ pieces) := fun plan => by
      letI : Decidable (∀ piece ∈ plan.pieces, piece ∈ pieces) :=
        List.decidableBAll (fun piece => piece ∈ pieces) plan.pieces
      infer_instance
    exact List.decidableBEx _ plans
  exact List.decidableBAll _ sources

/-- One semantic transition consumes the complete original source/neighbor
covers and checked outside-block pieces. It introduces no geometric premise. -/
theorem step_sound {u v : Nat} (d : Dictionary r m a)
    (positive : ∀ i, 0 < d.denominators i)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (sources neighbors pieces : List (Fin m)) (plans : List (Plan m))
    (sourceContexts : Fin u → PoseContext d) (neighborContexts : Fin v → PoseContext d)
    (covered : StepCover sources pieces plans)
    (plans_checked : ∀ plan ∈ plans, plan.Check d blockRows complement)
    (source_matches : ∀ plan ∈ plans, ∀ block, plan.block = some block →
      ∃ i, (sourceContexts i).pose = plan.source ∧ (sourceContexts i).block = blockRows block)
    (neighbor_complete : ∀ pose ∈ neighbors, ∃ j, (neighborContexts j).pose = pose)
    (neighbor_unblocked : ∀ j, (neighborContexts j).block = [])
    (pairs_checked : ∀ i j, (sourceContexts i).PairCheck (neighborContexts j) keys opposite)
    (q t : OpenSquare) (hq : OrientedPoseCovered (sources.map d.pose) q)
    (ht : OrientedPoseCovered (neighbors.map d.pose) t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered (pieces.map d.pose) q := by
  obtain ⟨source, member, realizes⟩ := hq
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member
  obtain ⟨plan, hp, he, hpieces⟩ := covered source in_sources
  have plan_realizes : (d.pose plan.source).OrientedRealizes q := by
    simpa only [he] using realizes
  have forbidden : ∀ block, plan.block = some block →
      ¬(∀ i ∈ blockRows block, (d.rows i).Holds ![centerX q, centerY q]) := by
    intro block hb
    obtain ⟨i, hi, hblock⟩ := source_matches plan hp block hb
    have hf := (sourceContexts i).block_forbidden positive keys opposite
      neighborContexts neighbors neighbor_complete neighbor_unblocked (pairs_checked i) q t
      (by simpa only [hi] using plan_realizes.1) ht disjoint
    simpa only [hblock] using hf
  obtain ⟨piece, member, realizes⟩ := plan.sound d blockRows complement positive
    (plans_checked plan hp) q plan_realizes forbidden
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  exact ⟨d.pose piece, List.mem_map.mpr ⟨piece, hpieces piece in_pieces, rfl⟩, realizes⟩

#print axioms PoseContext.pair_sound
#print axioms step_sound
end N12Compact.IndexedCachedPairPlans
