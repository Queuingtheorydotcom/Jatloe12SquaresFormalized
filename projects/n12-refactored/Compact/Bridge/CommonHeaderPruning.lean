import Compact.Bridge.CommonGroupPruning

/-! Common-point and axis groups discharge overlap from the exact source/block
header alone. The exclusion argument does not depend on how a pruning plan
represents its surviving targets. This interface supports both the historical
outside-branch plan and its smaller whole-target replacement.
-/

set_option Elab.async false

namespace N12Compact.IndexedCommonGroups
open S12 S12Pilot IntegerSupport IndexedRelaxation

variable {r m a u v : Nat} {d : Dictionary r m a}

def HeaderOverlap (d : Dictionary r m a) (domain : List (Fin m))
    (plan : Fin m × Option (List (Fin r))) : Prop :=
  ∀ q t : OpenSquare,
    (d.pose plan.1).OrientedRealizes q →
    OrientedPoseCovered (domain.map d.pose) t →
    ∀ block, plan.2 = some block →
      (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q]) →
      ∃ x y, q.Inside x y ∧ t.Inside x y

/-- Exact headers, full neighbor coverage and checked pair overlaps suffice;
no target pose or outside-branch representation is used. -/
theorem block_overlap_headers
    (sources : Fin u → Context d) (neighbors : Fin v → Context d)
    (domain : List (Fin m)) (headers : List (Header d))
    (headers_exact : headers = (List.finRange u).map (fun i => (sources i).header))
    (planHeaders : List (Fin m × Option (List (Fin r))))
    (checked : ∀ plan ∈ planHeaders, SourceCheck headers plan)
    (neighbors_exact : (List.finRange v).map (fun j => (neighbors j).header.pose) = domain)
    (unblocked : ∀ j, (neighbors j).header.block = [])
    (overlaps : ∀ i j, PairOverlaps (sources i) (neighbors j)) :
    ∀ plan ∈ planHeaders, HeaderOverlap d domain plan := by
  intro plan member q t hq ht block blocked holds
  have matched := checked plan member
  simp only [SourceCheck, blocked] at matched
  obtain ⟨header, in_headers, hp, hb⟩ := matched
  rw [headers_exact] at in_headers
  obtain ⟨i, _, hi⟩ := List.mem_map.mp in_headers
  have hpose : (sources i).header.pose = plan.1 := by rw [hi]; exact hp
  have hblock : (sources i).header.block = block := by rw [hi]; exact hb
  apply overlap_covered neighbors (sources i) domain ?_ unblocked (overlaps i) q t ?_ ht
  · intro pose member
    rw [← neighbors_exact] at member
    obtain ⟨j, _, hj⟩ := List.mem_map.mp member
    exact ⟨j, hj⟩
  · constructor
    · simpa only [hpose] using hq.1
    · simpa only [hblock] using holds

/-- The unchanged concrete stage can expose any plan type, provided its exact
ordered source/block projection agrees with the checked header list. -/
theorem block_overlap_map {Plan : Type} (plans : List Plan)
    (header : Plan → Fin m × Option (List (Fin r)))
    (planHeaders : List (Fin m × Option (List (Fin r))))
    (exact_headers : plans.map header = planHeaders) (domain : List (Fin m))
    (checked : ∀ plan ∈ planHeaders, HeaderOverlap d domain plan) :
    ∀ plan ∈ plans, HeaderOverlap d domain (header plan) := by
  intro plan member
  apply checked (header plan)
  rw [← exact_headers]
  exact List.mem_map.mpr ⟨plan, member, rfl⟩

#print axioms block_overlap_headers
#print axioms block_overlap_map
end N12Compact.IndexedCommonGroups
