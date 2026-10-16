import Compact.Cases.C898.CachedPairs.Step03Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step3_source_pose_exact (i : Fin 7) :
    (step3Sources i).pose = step3SourcePoseIds i := by fin_cases i <;> rfl

theorem step3_source_block_exact (i : Fin 7) :
    (step3Sources i).block = blockRows (step3SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step3_neighbor_pose_exact (j : Fin 64) :
    (step3Neighbors j).pose = step3NeighborPoseIds j := by fin_cases j <;> rfl

theorem step3_plans_checked : ∀ plan ∈ step3Plans, plan.Check complement := by
  decide +kernel

theorem step3_cover : StepCover continuousScout898Domain6_0Ids step3Pieces step3Plans := by
  decide +kernel

theorem step3_source_matches :
    ∀ plan ∈ step3Plans, ∀ block, plan.block = some block →
      ∃ i, (step3Sources i).pose = plan.source ∧
        (step3Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step3Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step3_source_pose_exact 0,
      step3_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step3_source_pose_exact 1,
      step3_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step3_source_pose_exact 2,
      step3_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step3_source_pose_exact 3,
      step3_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step3_source_pose_exact 4,
      step3_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step3_source_pose_exact 5,
      step3_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step3_source_pose_exact 6,
      step3_source_block_exact 6⟩
  · cases hb

private theorem step3_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain3_3Ids,
    ∃ j, step3NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 64).map step3NeighborPoseIds =
      continuousScout898Domain3_3Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step3_neighbor_complete : ∀ pose ∈ continuousScout898Domain3_3Ids,
    ∃ j, (step3Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step3_neighbor_ids_complete pose member
  exact ⟨j,(step3_neighbor_pose_exact j).trans hj⟩

theorem step3_neighbor_unblocked : ∀ j, (step3Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step3LinkTargetIds : List (Fin poseCount) :=
  [2260, 2262, 2264, 2266, 2268, 2270, 2272, 2274, 2276, 2278, 2280, 2282, 2284, 2284, 2287]

theorem step3_link_targets_mem :
    step3LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain6_4Ids)) = true := by
  decide +kernel

theorem step3_links_checked :
    ∀ piece ∈ step3Pieces, ∃ i ∈ step3Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain6_4Ids := by
  have exact_sources : step3Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step3Pieces := by rfl
  have exact_targets : step3Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step3LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step3LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step3_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
