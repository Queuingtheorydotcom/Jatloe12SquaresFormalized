import Compact.Cases.C898.CachedPairFan
import Compact.Cases.C898.SharedDictionary

/-! Record-free pruning assembly. A plan stores its source, optional block,
and surviving pieces. Whole-neighbor overlap coverage is supplied by the
checked Cartesian fan family, not a repeated list of pair-record indices.
The actual source and neighbor square hypotheses remain unchanged.
-/

set_option Elab.async false

namespace N12Compact.C898Cached
open S12 S12Pilot IntegerSupport PairPruning C898Shared

structure Plan where
  source : Fin poseCount
  block : Option Nat
  pieces : List (Fin poseCount)

noncomputable def Plan.contexts (plan : Plan) (complement : Fin rowCount → Fin rowCount) :
    List (List (Fin rowCount)) :=
  match plan.block with
  | none => [poseRows plan.source]
  | some block => outsidePieces complement (blockRows block) (poseRows plan.source)

noncomputable def Plan.Check (plan : Plan) (complement : Fin rowCount → Fin rowCount) : Prop :=
  (∀ context ∈ plan.contexts complement, ∃ piece ∈ plan.pieces,
    poseRows piece = context ∧ poseAngle plan.source = poseAngle piece) ∧
  match plan.block with
  | none => True
  | some block => ∀ i ∈ blockRows block, rows (complement i) = RegionDAG.opposite (rows i)

noncomputable instance planDecidableCheck (plan : Plan) (complement : Fin rowCount → Fin rowCount) :
    Decidable (plan.Check complement) := by
  unfold Plan.Check
  letI : DecidablePred (fun context => ∃ piece ∈ plan.pieces,
      poseRows piece = context ∧ poseAngle plan.source = poseAngle piece) := fun context =>
    List.decidableBEx (fun piece =>
      poseRows piece = context ∧ poseAngle plan.source = poseAngle piece) plan.pieces
  letI : Decidable (∀ context ∈ plan.contexts complement, ∃ piece ∈ plan.pieces,
      poseRows piece = context ∧ poseAngle plan.source = poseAngle piece) :=
    List.decidableBAll _ (plan.contexts complement)
  cases plan.block with
  | none => infer_instance
  | some block =>
      letI : Decidable (∀ i ∈ blockRows block,
          rows (complement i) = RegionDAG.opposite (rows i)) :=
        List.decidableBAll _ (blockRows block)
      infer_instance

theorem PoseContext.block_forbidden {n : Nat} (source : PoseContext)
    (neighbors : Fin n → PoseContext) (domain : List (Fin poseCount))
    (complete : ∀ pose ∈ domain, ∃ j, (neighbors j).pose = pose)
    (unblocked : ∀ j, (neighbors j).block = [])
    (checked : ∀ j, source.PairCheck (neighbors j))
    (q t : OpenSquare) (hq : (poses source.pose).Realizes q)
    (ht : OrientedPoseCovered (domain.map poses) t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    ¬(∀ i ∈ source.block, (rows i).Holds ![centerX q, centerY q]) := by
  intro holds
  obtain ⟨neighbor, member, realizes⟩ := ht
  obtain ⟨neighbor, in_domain, rfl⟩ := List.mem_map.mp member
  obtain ⟨j, hj⟩ := complete neighbor in_domain
  obtain ⟨x, y, overlap⟩ := source.pair_sound (neighbors j) (checked j) q t hq
    (by simpa only [hj] using realizes.1) holds
    (by simp only [unblocked j, List.not_mem_nil, false_implies, forall_const])
  exact disjoint x y overlap

theorem Plan.sound (plan : Plan) (complement : Fin rowCount → Fin rowCount)
    (checked : plan.Check complement) (q : OpenSquare)
    (hq : (poses plan.source).OrientedRealizes q)
    (forbidden : ∀ block, plan.block = some block →
      ¬(∀ i ∈ blockRows block, (rows i).Holds ![centerX q, centerY q])) :
    OrientedPoseCovered (plan.pieces.map poses) q := by
  have incoming : ∀ i ∈ poseRows plan.source,
      (rows i).Holds ![centerX q, centerY q] :=
    inputs_hold rows denominators positive_denominators (poseRows plan.source) _ hq.1.1
  have surviving : ∃ context ∈ plan.contexts complement,
      ∀ i ∈ context, (rows i).Holds ![centerX q, centerY q] := by
    cases hblock : plan.block with
    | none => exact ⟨poseRows plan.source, by simp [Plan.contexts, hblock], incoming⟩
    | some block =>
        have hc := checked.2
        rw [hblock] at hc
        obtain ⟨context, member, holds⟩ := outsidePieces_sound rows complement
          (blockRows block) (poseRows plan.source) hc _ incoming (forbidden block hblock)
        exact ⟨context, by simpa only [Plan.contexts, hblock] using member, holds⟩
  obtain ⟨context, member, holds⟩ := surviving
  obtain ⟨piece, hpiece, hrows, hangle⟩ := checked.1 context member
  refine ⟨poses piece, List.mem_map.mpr ⟨piece, hpiece, rfl⟩, ?_⟩
  apply dictionary.transfer hangle positive_denominators q hq
  simpa only [dictionary, hrows] using holds

def StepCover (sources pieces : List (Fin poseCount)) (plans : List Plan) : Prop :=
  ∀ source ∈ sources, ∃ plan ∈ plans, plan.source = source ∧
    ∀ piece ∈ plan.pieces, piece ∈ pieces

instance (sources pieces : List (Fin poseCount)) (plans : List Plan) :
    Decidable (StepCover sources pieces plans) := by
  unfold StepCover
  letI : DecidablePred (fun source => ∃ plan ∈ plans, plan.source = source ∧
      ∀ piece ∈ plan.pieces, piece ∈ pieces) := fun source => by
    letI : DecidablePred (fun plan : Plan => plan.source = source ∧
        ∀ piece ∈ plan.pieces, piece ∈ pieces) := fun plan => by
      letI : Decidable (∀ piece ∈ plan.pieces, piece ∈ pieces) :=
        List.decidableBAll (fun piece => piece ∈ pieces) plan.pieces
      infer_instance
    exact List.decidableBEx _ plans
  exact List.decidableBAll _ sources

/-- Every blocked plan is linked to a complete checked family of neighbors.
Plans without a block only transfer their unchanged input constraints. -/
theorem step_sound {a b : Nat}
    (sources neighbors pieces : List (Fin poseCount)) (plans : List Plan)
    (complement : Fin rowCount → Fin rowCount)
    (sourceContexts : Fin a → PoseContext) (neighborContexts : Fin b → PoseContext)
    (covered : StepCover sources pieces plans)
    (plans_checked : ∀ plan ∈ plans, plan.Check complement)
    (source_matches : ∀ plan ∈ plans, ∀ block, plan.block = some block →
      ∃ i, (sourceContexts i).pose = plan.source ∧ (sourceContexts i).block = blockRows block)
    (neighbor_complete : ∀ pose ∈ neighbors, ∃ j, (neighborContexts j).pose = pose)
    (neighbor_unblocked : ∀ j, (neighborContexts j).block = [])
    (pairs_checked : ∀ i j, (sourceContexts i).PairCheck (neighborContexts j))
    (q t : OpenSquare) (hq : OrientedPoseCovered (sources.map poses) q)
    (ht : OrientedPoseCovered (neighbors.map poses) t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered (pieces.map poses) q := by
  obtain ⟨source, member, realizes⟩ := hq
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member
  obtain ⟨plan, hp, he, hpieces⟩ := covered source in_sources
  have plan_realizes : (poses plan.source).OrientedRealizes q := by
    simpa only [he] using realizes
  have forbidden : ∀ block, plan.block = some block →
      ¬(∀ i ∈ blockRows block, (rows i).Holds ![centerX q, centerY q]) := by
    intro block hb
    obtain ⟨i, hi, hblock⟩ := source_matches plan hp block hb
    have hf := (sourceContexts i).block_forbidden neighborContexts neighbors
      neighbor_complete neighbor_unblocked (pairs_checked i) q t
      (by simpa only [hi] using plan_realizes.1) ht disjoint
    simpa only [hblock] using hf
  obtain ⟨piece, member, realizes⟩ := plan.sound complement (plans_checked plan hp)
    q plan_realizes forbidden
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  exact ⟨poses piece, List.mem_map.mpr ⟨piece, hpieces piece in_pieces, rfl⟩, realizes⟩

#print axioms step_sound
end N12Compact.C898Cached
