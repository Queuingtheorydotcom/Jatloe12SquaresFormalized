import Compact.Cases.C898.CachedPairs.Step06Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step6_source_pose_exact (i : Fin 59) :
    (step6Sources i).pose = step6SourcePoseIds i := by fin_cases i <;> rfl

theorem step6_source_block_exact (i : Fin 59) :
    (step6Sources i).block = blockRows (step6SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step6_neighbor_pose_exact (j : Fin 59) :
    (step6Neighbors j).pose = step6NeighborPoseIds j := by fin_cases j <;> rfl

theorem step6_plans_checked : ∀ plan ∈ step6Plans, plan.Check complement := by
  decide +kernel

theorem step6_cover : StepCover continuousScout898Domain7_6Ids step6Pieces step6Plans := by
  decide +kernel

theorem step6_source_matches :
    ∀ plan ∈ step6Plans, ∀ block, plan.block = some block →
      ∃ i, (step6Sources i).pose = plan.source ∧
        (step6Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step6Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step6_source_pose_exact 0,
      step6_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step6_source_pose_exact 1,
      step6_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step6_source_pose_exact 2,
      step6_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step6_source_pose_exact 3,
      step6_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step6_source_pose_exact 4,
      step6_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step6_source_pose_exact 5,
      step6_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step6_source_pose_exact 6,
      step6_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step6_source_pose_exact 7,
      step6_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step6_source_pose_exact 8,
      step6_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step6_source_pose_exact 9,
      step6_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step6_source_pose_exact 10,
      step6_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step6_source_pose_exact 11,
      step6_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step6_source_pose_exact 12,
      step6_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step6_source_pose_exact 13,
      step6_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step6_source_pose_exact 14,
      step6_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step6_source_pose_exact 15,
      step6_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step6_source_pose_exact 16,
      step6_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step6_source_pose_exact 17,
      step6_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step6_source_pose_exact 18,
      step6_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step6_source_pose_exact 19,
      step6_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step6_source_pose_exact 20,
      step6_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step6_source_pose_exact 21,
      step6_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step6_source_pose_exact 22,
      step6_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step6_source_pose_exact 23,
      step6_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step6_source_pose_exact 24,
      step6_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step6_source_pose_exact 25,
      step6_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step6_source_pose_exact 26,
      step6_source_block_exact 26⟩
  · cases hb
  · cases hb
    exact ⟨27, step6_source_pose_exact 27,
      step6_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step6_source_pose_exact 28,
      step6_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step6_source_pose_exact 29,
      step6_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step6_source_pose_exact 30,
      step6_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step6_source_pose_exact 31,
      step6_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step6_source_pose_exact 32,
      step6_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step6_source_pose_exact 33,
      step6_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step6_source_pose_exact 34,
      step6_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step6_source_pose_exact 35,
      step6_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step6_source_pose_exact 36,
      step6_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step6_source_pose_exact 37,
      step6_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step6_source_pose_exact 38,
      step6_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step6_source_pose_exact 39,
      step6_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step6_source_pose_exact 40,
      step6_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step6_source_pose_exact 41,
      step6_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step6_source_pose_exact 42,
      step6_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step6_source_pose_exact 43,
      step6_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step6_source_pose_exact 44,
      step6_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step6_source_pose_exact 45,
      step6_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step6_source_pose_exact 46,
      step6_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step6_source_pose_exact 47,
      step6_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step6_source_pose_exact 48,
      step6_source_block_exact 48⟩
  · cases hb
    exact ⟨49, step6_source_pose_exact 49,
      step6_source_block_exact 49⟩
  · cases hb
    exact ⟨50, step6_source_pose_exact 50,
      step6_source_block_exact 50⟩
  · cases hb
    exact ⟨51, step6_source_pose_exact 51,
      step6_source_block_exact 51⟩
  · cases hb
    exact ⟨52, step6_source_pose_exact 52,
      step6_source_block_exact 52⟩
  · cases hb
    exact ⟨53, step6_source_pose_exact 53,
      step6_source_block_exact 53⟩
  · cases hb
    exact ⟨54, step6_source_pose_exact 54,
      step6_source_block_exact 54⟩
  · cases hb
    exact ⟨55, step6_source_pose_exact 55,
      step6_source_block_exact 55⟩
  · cases hb
    exact ⟨56, step6_source_pose_exact 56,
      step6_source_block_exact 56⟩
  · cases hb
    exact ⟨57, step6_source_pose_exact 57,
      step6_source_block_exact 57⟩
  · cases hb
    exact ⟨58, step6_source_pose_exact 58,
      step6_source_block_exact 58⟩
  · cases hb

private theorem step6_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain11_0Ids,
    ∃ j, step6NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 59).map step6NeighborPoseIds =
      continuousScout898Domain11_0Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step6_neighbor_complete : ∀ pose ∈ continuousScout898Domain11_0Ids,
    ∃ j, (step6Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step6_neighbor_ids_complete pose member
  exact ⟨j,(step6_neighbor_pose_exact j).trans hj⟩

theorem step6_neighbor_unblocked : ∀ j, (step6Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step6LinkTargetIds : List (Fin poseCount) :=
  [2456, 2458, 2460, 2460, 2463, 2463, 2466, 2466, 2469, 2469, 2472, 2472, 2475, 2475, 2478, 2478, 2481, 2481, 2484, 2484, 2487, 2487, 2490, 2490, 2493, 2493, 2496, 2496, 2499, 2499, 2502, 2502, 2505, 2505, 2508, 2508, 2508, 2512, 2514, 2516, 2518, 2520, 2522, 2524, 2526, 2528, 2530, 2532, 2534, 2536, 2538, 2540, 2542, 2544, 2546, 2548, 2550, 2550, 2553, 2553, 2556, 2556, 2559, 2559, 2562, 2562, 2565, 2565, 2568, 2568, 2571, 2571, 2574, 2574, 2577, 2577, 2580, 2580, 2583, 2583, 2586, 2586, 2586, 2590, 2590, 2590, 2594, 2594, 2594, 2598, 2598, 2598, 2602, 2602, 2602, 2606, 2606, 2609, 2609, 2612, 2612, 2615, 2615, 2618, 2618, 2621, 2621, 2624, 2624, 2627]

theorem step6_link_targets_mem :
    step6LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain7_7Ids)) = true := by
  decide +kernel

theorem step6_links_checked :
    ∀ piece ∈ step6Pieces, ∃ i ∈ step6Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain7_7Ids := by
  have exact_sources : step6Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step6Pieces := by rfl
  have exact_targets : step6Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step6LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step6LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step6_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
