import Compact.Cases.C898.CachedPairPlans

/-! Pruning needs actual overlap, independently of the certificate used to
prove it. This version accepts shared-point proofs or ordinary axis proofs
without replacing either by additional numerical premises. -/

set_option Elab.async false

namespace N12Compact.C898Cached
open S12 S12Pilot IntegerSupport PairPruning C898Shared

theorem step_sound_of_overlap {a b : Nat}
    (sources neighbors pieces : List (Fin poseCount)) (plans : List Plan)
    (complement : Fin rowCount → Fin rowCount)
    (sourceContexts : Fin a → PoseContext) (neighborContexts : Fin b → PoseContext)
    (covered : StepCover sources pieces plans)
    (plans_checked : ∀ plan ∈ plans, plan.Check complement)
    (source_matches : ∀ plan ∈ plans, ∀ block, plan.block = some block →
      ∃ i, (sourceContexts i).pose = plan.source ∧ (sourceContexts i).block = blockRows block)
    (neighbor_complete : ∀ pose ∈ neighbors, ∃ j, (neighborContexts j).pose = pose)
    (overlap : ∀ i j (q t : OpenSquare),
      (poses (sourceContexts i).pose).Realizes q →
      (poses (neighborContexts j).pose).Realizes t →
      (∀ k ∈ (sourceContexts i).block, (rows k).Holds ![centerX q, centerY q]) →
      ∃ x y, q.Inside x y ∧ t.Inside x y)
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
    intro block hb holds
    obtain ⟨i, hi, hblock⟩ := source_matches plan hp block hb
    obtain ⟨neighbor, member, neighbor_realizes⟩ := ht
    obtain ⟨neighbor, in_neighbors, rfl⟩ := List.mem_map.mp member
    obtain ⟨j, hj⟩ := neighbor_complete neighbor in_neighbors
    obtain ⟨x, y, intersects⟩ := overlap i j q t
      (by simpa only [hi] using plan_realizes.1)
      (by simpa only [hj] using neighbor_realizes.1)
      (by simpa only [hblock] using holds)
    exact disjoint x y intersects
  obtain ⟨piece, member, realizes⟩ := plan.sound complement (plans_checked plan hp)
    q plan_realizes forbidden
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  exact ⟨poses piece, List.mem_map.mpr ⟨piece, hpieces piece in_pieces, rfl⟩, realizes⟩

#print axioms step_sound_of_overlap

end N12Compact.C898Cached
