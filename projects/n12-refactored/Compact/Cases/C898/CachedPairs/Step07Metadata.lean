import Compact.Cases.C898.CachedPairs.Step07Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step7_source_pose_exact (i : Fin 49) :
    (step7Sources i).pose = step7SourcePoseIds i := by fin_cases i <;> rfl

theorem step7_source_block_exact (i : Fin 49) :
    (step7Sources i).block = blockRows (step7SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step7_neighbor_pose_exact (j : Fin 64) :
    (step7Neighbors j).pose = step7NeighborPoseIds j := by fin_cases j <;> rfl

theorem step7_plans_checked : ∀ plan ∈ step7Plans, plan.Check complement := by
  decide +kernel

theorem step7_cover : StepCover continuousScout898Domain9_0Ids step7Pieces step7Plans := by
  decide +kernel

theorem step7_source_matches :
    ∀ plan ∈ step7Plans, ∀ block, plan.block = some block →
      ∃ i, (step7Sources i).pose = plan.source ∧
        (step7Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step7Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step7_source_pose_exact 0,
      step7_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step7_source_pose_exact 1,
      step7_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step7_source_pose_exact 2,
      step7_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step7_source_pose_exact 3,
      step7_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step7_source_pose_exact 4,
      step7_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step7_source_pose_exact 5,
      step7_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step7_source_pose_exact 6,
      step7_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step7_source_pose_exact 7,
      step7_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step7_source_pose_exact 8,
      step7_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step7_source_pose_exact 9,
      step7_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step7_source_pose_exact 10,
      step7_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step7_source_pose_exact 11,
      step7_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step7_source_pose_exact 12,
      step7_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step7_source_pose_exact 13,
      step7_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step7_source_pose_exact 14,
      step7_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step7_source_pose_exact 15,
      step7_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step7_source_pose_exact 16,
      step7_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step7_source_pose_exact 17,
      step7_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step7_source_pose_exact 18,
      step7_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step7_source_pose_exact 19,
      step7_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step7_source_pose_exact 20,
      step7_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step7_source_pose_exact 21,
      step7_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step7_source_pose_exact 22,
      step7_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step7_source_pose_exact 23,
      step7_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step7_source_pose_exact 24,
      step7_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step7_source_pose_exact 25,
      step7_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step7_source_pose_exact 26,
      step7_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step7_source_pose_exact 27,
      step7_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step7_source_pose_exact 28,
      step7_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step7_source_pose_exact 29,
      step7_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step7_source_pose_exact 30,
      step7_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step7_source_pose_exact 31,
      step7_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step7_source_pose_exact 32,
      step7_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step7_source_pose_exact 33,
      step7_source_block_exact 33⟩
  · cases hb
  · cases hb
  · cases hb
    exact ⟨34, step7_source_pose_exact 34,
      step7_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step7_source_pose_exact 35,
      step7_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step7_source_pose_exact 36,
      step7_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step7_source_pose_exact 37,
      step7_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step7_source_pose_exact 38,
      step7_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step7_source_pose_exact 39,
      step7_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step7_source_pose_exact 40,
      step7_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step7_source_pose_exact 41,
      step7_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step7_source_pose_exact 42,
      step7_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step7_source_pose_exact 43,
      step7_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step7_source_pose_exact 44,
      step7_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step7_source_pose_exact 45,
      step7_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step7_source_pose_exact 46,
      step7_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step7_source_pose_exact 47,
      step7_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step7_source_pose_exact 48,
      step7_source_block_exact 48⟩
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb

private theorem step7_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain2_2Ids,
    ∃ j, step7NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 64).map step7NeighborPoseIds =
      continuousScout898Domain2_2Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step7_neighbor_complete : ∀ pose ∈ continuousScout898Domain2_2Ids,
    ∃ j, (step7Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step7_neighbor_ids_complete pose member
  exact ⟨j,(step7_neighbor_pose_exact j).trans hj⟩

theorem step7_neighbor_unblocked : ∀ j, (step7Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step7LinkTargetIds : List (Fin poseCount) :=
  [2629, 2631, 2633, 2633, 2636, 2636, 2639, 2639, 2642, 2642, 2645, 2645, 2648, 2648, 2651, 2651, 2654, 2654, 2657, 2657, 2660, 2660, 2663, 2663, 2666, 2666, 2669, 2671, 2673, 2675, 2677, 2679, 2681, 2683, 2685, 2687, 2689, 2691, 2693, 2695, 2697, 2699, 2701, 2703, 2705, 2705, 2708, 2708, 2711, 2711, 2714, 2714, 2717, 2717, 2720, 2720, 2723, 2723, 2726, 2726, 2729, 2729, 2732, 2732, 2735, 2735, 2738, 2738, 2741, 2741, 2744, 2744, 2747, 2747, 2750, 2752, 2754, 2756, 2758, 2760]

theorem step7_link_targets_mem :
    step7LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain9_8Ids)) = true := by
  decide +kernel

theorem step7_links_checked :
    ∀ piece ∈ step7Pieces, ∃ i ∈ step7Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain9_8Ids := by
  have exact_sources : step7Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step7Pieces := by rfl
  have exact_targets : step7Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step7LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step7LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step7_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
