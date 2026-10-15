import Compact.Cases.C898.CachedPairs.Step12Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step12_source_pose_exact (i : Fin 49) :
    (step12Sources i).pose = step12SourcePoseIds i := by fin_cases i <;> rfl

theorem step12_source_block_exact (i : Fin 49) :
    (step12Sources i).block = blockRows (step12SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step12_neighbor_pose_exact (j : Fin 12) :
    (step12Neighbors j).pose = step12NeighborPoseIds j := by fin_cases j <;> rfl

theorem step12_plans_checked : ∀ plan ∈ step12Plans, plan.Check complement := by
  decide +kernel

theorem step12_cover : StepCover continuousScout898Domain5_12Ids step12Pieces step12Plans := by
  decide +kernel

theorem step12_source_matches :
    ∀ plan ∈ step12Plans, ∀ block, plan.block = some block →
      ∃ i, (step12Sources i).pose = plan.source ∧
        (step12Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step12Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
    exact ⟨0, step12_source_pose_exact 0,
      step12_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step12_source_pose_exact 1,
      step12_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step12_source_pose_exact 2,
      step12_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step12_source_pose_exact 3,
      step12_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step12_source_pose_exact 4,
      step12_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step12_source_pose_exact 5,
      step12_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step12_source_pose_exact 6,
      step12_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step12_source_pose_exact 7,
      step12_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step12_source_pose_exact 8,
      step12_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step12_source_pose_exact 9,
      step12_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step12_source_pose_exact 10,
      step12_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step12_source_pose_exact 11,
      step12_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step12_source_pose_exact 12,
      step12_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step12_source_pose_exact 13,
      step12_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step12_source_pose_exact 14,
      step12_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step12_source_pose_exact 15,
      step12_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step12_source_pose_exact 16,
      step12_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step12_source_pose_exact 17,
      step12_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step12_source_pose_exact 18,
      step12_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step12_source_pose_exact 19,
      step12_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step12_source_pose_exact 20,
      step12_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step12_source_pose_exact 21,
      step12_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step12_source_pose_exact 22,
      step12_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step12_source_pose_exact 23,
      step12_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step12_source_pose_exact 24,
      step12_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step12_source_pose_exact 25,
      step12_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step12_source_pose_exact 26,
      step12_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step12_source_pose_exact 27,
      step12_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step12_source_pose_exact 28,
      step12_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step12_source_pose_exact 29,
      step12_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step12_source_pose_exact 30,
      step12_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step12_source_pose_exact 31,
      step12_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step12_source_pose_exact 32,
      step12_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step12_source_pose_exact 33,
      step12_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step12_source_pose_exact 34,
      step12_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step12_source_pose_exact 35,
      step12_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step12_source_pose_exact 36,
      step12_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step12_source_pose_exact 37,
      step12_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step12_source_pose_exact 38,
      step12_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step12_source_pose_exact 39,
      step12_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step12_source_pose_exact 40,
      step12_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step12_source_pose_exact 41,
      step12_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step12_source_pose_exact 42,
      step12_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step12_source_pose_exact 43,
      step12_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step12_source_pose_exact 44,
      step12_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step12_source_pose_exact 45,
      step12_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step12_source_pose_exact 46,
      step12_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step12_source_pose_exact 47,
      step12_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step12_source_pose_exact 48,
      step12_source_block_exact 48⟩

private theorem step12_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain6_5Ids,
    ∃ j, step12NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 12).map step12NeighborPoseIds =
      continuousScout898Domain6_5Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step12_neighbor_complete : ∀ pose ∈ continuousScout898Domain6_5Ids,
    ∃ j, (step12Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step12_neighbor_ids_complete pose member
  exact ⟨j,(step12_neighbor_pose_exact j).trans hj⟩

theorem step12_neighbor_unblocked : ∀ j, (step12Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step12LinkTargetIds : List (Fin poseCount) :=
  [3255, 3257, 3259, 3261, 3263, 3265, 3267, 3269, 3271, 3273, 3275, 3277, 3279, 3281, 3283, 3285, 3287, 3289, 3291, 3293, 3295, 3297, 3299]

theorem step12_link_targets_mem :
    step12LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain5_13Ids)) = true := by
  decide +kernel

theorem step12_links_checked :
    ∀ piece ∈ step12Pieces, ∃ i ∈ step12Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain5_13Ids := by
  have exact_sources : step12Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step12Pieces := by rfl
  have exact_targets : step12Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step12LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step12LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step12_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
