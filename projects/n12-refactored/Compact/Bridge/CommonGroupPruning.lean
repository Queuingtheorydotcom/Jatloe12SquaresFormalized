import Compact.Bridge.IndexedCommonGroups
import Compact.Bridge.DirectPruningPlan

/-! Small metadata checks connect complete common-point rectangles to the
unchanged original pruning plans. Numeric fan proofs are not unfolded by the
plan/neighbor coverage checks. -/

set_option Elab.async false

namespace N12Compact.IndexedCommonGroups
open S12 S12Pilot IntegerSupport IndexedRelaxation DirectPruningPlan

variable {r m a u v : Nat} {d : Dictionary r m a}

def SourceCheck (headers : List (Header d))
    (plan : Fin m × Option (List (Fin r))) : Prop :=
  match plan.2 with
  | none => True
  | some block => ∃ header ∈ headers, header.pose = plan.1 ∧ header.block = block

instance (headers : List (Header d)) (plan : Fin m × Option (List (Fin r))) :
    Decidable (SourceCheck headers plan) := by
  unfold SourceCheck
  split
  · infer_instance
  · exact List.decidableBEx _ headers

/-- Every blocked source is matched by its exact pose and complete block;
every original neighbor remains in the coverage list. -/
theorem block_overlap
    (sources : Fin u → Context d) (neighbors : Fin v → Context d)
    (plans : List (Plan r m)) (domain : List (Fin m))
    (headers : List (Header d))
    (headers_exact : headers = (List.finRange u).map (fun i => (sources i).header))
    (planHeaders : List (Fin m × Option (List (Fin r))))
    (plans_exact : plans.map (fun plan => (plan.source, plan.block)) = planHeaders)
    (checked : ∀ plan ∈ planHeaders, SourceCheck headers plan)
    (neighbors_exact : (List.finRange v).map (fun j => (neighbors j).header.pose) = domain)
    (unblocked : ∀ j, (neighbors j).header.block = [])
    (overlaps : ∀ i j, PairOverlaps (sources i) (neighbors j)) :
    ∀ plan ∈ plans, ∀ q t : OpenSquare,
      (d.pose plan.source).OrientedRealizes q →
      OrientedPoseCovered (domain.map d.pose) t →
      ∀ block, plan.block = some block →
        (∀ i ∈ block, (d.rows i).Holds ![centerX q, centerY q]) →
        ∃ x y, q.Inside x y ∧ t.Inside x y := by
  intro plan member q t hq ht block blocked holds
  have plan_member : (plan.source, plan.block) ∈ planHeaders := by
    rw [← plans_exact]
    exact List.mem_map.mpr ⟨plan, member, rfl⟩
  have matched := checked _ plan_member
  simp only [SourceCheck, blocked] at matched
  obtain ⟨header, in_headers, hp, hb⟩ := matched
  rw [headers_exact] at in_headers
  obtain ⟨i, _, hi⟩ := List.mem_map.mp in_headers
  have hpose : (sources i).header.pose = plan.source := by rw [hi]; exact hp
  have hblock : (sources i).header.block = block := by rw [hi]; exact hb
  apply overlap_covered neighbors (sources i) domain ?_ unblocked (overlaps i) q t ?_ ht
  · intro pose member
    rw [← neighbors_exact] at member
    obtain ⟨j, _, hj⟩ := List.mem_map.mp member
    exact ⟨j, hj⟩
  · constructor
    · simpa only [hpose] using hq.1
    · simpa only [hblock] using holds

#print axioms block_overlap
end N12Compact.IndexedCommonGroups
