import Compact.Cases.C898.CachedPairs.Step04Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step4_source_pose_exact (i : Fin 7) :
    (step4Sources i).pose = step4SourcePoseIds i := by fin_cases i <;> rfl

theorem step4_source_block_exact (i : Fin 7) :
    (step4Sources i).block = blockRows (step4SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step4_neighbor_pose_exact (j : Fin 64) :
    (step4Neighbors j).pose = step4NeighborPoseIds j := by fin_cases j <;> rfl

theorem step4_plans_checked : ∀ plan ∈ step4Plans, plan.Check complement := by
  decide +kernel

theorem step4_cover : StepCover continuousScout898Domain6_4Ids step4Pieces step4Plans := by
  decide +kernel

theorem step4_source_matches :
    ∀ plan ∈ step4Plans, ∀ block, plan.block = some block →
      ∃ i, (step4Sources i).pose = plan.source ∧
        (step4Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step4Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step4_source_pose_exact 0,
      step4_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step4_source_pose_exact 1,
      step4_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step4_source_pose_exact 2,
      step4_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step4_source_pose_exact 3,
      step4_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step4_source_pose_exact 4,
      step4_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step4_source_pose_exact 5,
      step4_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step4_source_pose_exact 6,
      step4_source_block_exact 6⟩
  · cases hb

private theorem step4_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain10_0Ids,
    ∃ j, step4NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 64).map step4NeighborPoseIds =
      continuousScout898Domain10_0Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step4_neighbor_complete : ∀ pose ∈ continuousScout898Domain10_0Ids,
    ∃ j, (step4Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step4_neighbor_ids_complete pose member
  exact ⟨j,(step4_neighbor_pose_exact j).trans hj⟩

theorem step4_neighbor_unblocked : ∀ j, (step4Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step4LinkTargetIds : List (Fin poseCount) :=
  [2289, 2291, 2293, 2295, 2297, 2299, 2301, 2303, 2305, 2307, 2309, 2311]

theorem step4_link_targets_mem :
    step4LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain6_5Ids)) = true := by
  decide +kernel

theorem step4_links_checked :
    ∀ piece ∈ step4Pieces, ∃ i ∈ step4Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain6_5Ids := by
  have exact_sources : step4Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step4Pieces := by rfl
  have exact_targets : step4Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step4LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step4LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step4_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
