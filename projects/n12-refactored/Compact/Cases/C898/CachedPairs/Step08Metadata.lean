import Compact.Cases.C898.CachedPairs.Step08Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step8_source_pose_exact (i : Fin 64) :
    (step8Sources i).pose = step8SourcePoseIds i := by fin_cases i <;> rfl

theorem step8_source_block_exact (i : Fin 64) :
    (step8Sources i).block = blockRows (step8SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step8_neighbor_pose_exact (j : Fin 64) :
    (step8Neighbors j).pose = step8NeighborPoseIds j := by fin_cases j <;> rfl

theorem step8_plans_checked : ∀ plan ∈ step8Plans, plan.Check complement := by
  decide +kernel

theorem step8_cover : StepCover continuousScout898Domain0_0Ids step8Pieces step8Plans := by
  decide +kernel

theorem step8_source_matches :
    ∀ plan ∈ step8Plans, ∀ block, plan.block = some block →
      ∃ i, (step8Sources i).pose = plan.source ∧
        (step8Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step8Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
    exact ⟨0, step8_source_pose_exact 0,
      step8_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step8_source_pose_exact 1,
      step8_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step8_source_pose_exact 2,
      step8_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step8_source_pose_exact 3,
      step8_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step8_source_pose_exact 4,
      step8_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step8_source_pose_exact 5,
      step8_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step8_source_pose_exact 6,
      step8_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step8_source_pose_exact 7,
      step8_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step8_source_pose_exact 8,
      step8_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step8_source_pose_exact 9,
      step8_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step8_source_pose_exact 10,
      step8_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step8_source_pose_exact 11,
      step8_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step8_source_pose_exact 12,
      step8_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step8_source_pose_exact 13,
      step8_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step8_source_pose_exact 14,
      step8_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step8_source_pose_exact 15,
      step8_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step8_source_pose_exact 16,
      step8_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step8_source_pose_exact 17,
      step8_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step8_source_pose_exact 18,
      step8_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step8_source_pose_exact 19,
      step8_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step8_source_pose_exact 20,
      step8_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step8_source_pose_exact 21,
      step8_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step8_source_pose_exact 22,
      step8_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step8_source_pose_exact 23,
      step8_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step8_source_pose_exact 24,
      step8_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step8_source_pose_exact 25,
      step8_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step8_source_pose_exact 26,
      step8_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step8_source_pose_exact 27,
      step8_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step8_source_pose_exact 28,
      step8_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step8_source_pose_exact 29,
      step8_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step8_source_pose_exact 30,
      step8_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step8_source_pose_exact 31,
      step8_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step8_source_pose_exact 32,
      step8_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step8_source_pose_exact 33,
      step8_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step8_source_pose_exact 34,
      step8_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step8_source_pose_exact 35,
      step8_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step8_source_pose_exact 36,
      step8_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step8_source_pose_exact 37,
      step8_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step8_source_pose_exact 38,
      step8_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step8_source_pose_exact 39,
      step8_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step8_source_pose_exact 40,
      step8_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step8_source_pose_exact 41,
      step8_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step8_source_pose_exact 42,
      step8_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step8_source_pose_exact 43,
      step8_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step8_source_pose_exact 44,
      step8_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step8_source_pose_exact 45,
      step8_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step8_source_pose_exact 46,
      step8_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step8_source_pose_exact 47,
      step8_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step8_source_pose_exact 48,
      step8_source_block_exact 48⟩
  · cases hb
    exact ⟨49, step8_source_pose_exact 49,
      step8_source_block_exact 49⟩
  · cases hb
    exact ⟨50, step8_source_pose_exact 50,
      step8_source_block_exact 50⟩
  · cases hb
    exact ⟨51, step8_source_pose_exact 51,
      step8_source_block_exact 51⟩
  · cases hb
    exact ⟨52, step8_source_pose_exact 52,
      step8_source_block_exact 52⟩
  · cases hb
    exact ⟨53, step8_source_pose_exact 53,
      step8_source_block_exact 53⟩
  · cases hb
    exact ⟨54, step8_source_pose_exact 54,
      step8_source_block_exact 54⟩
  · cases hb
    exact ⟨55, step8_source_pose_exact 55,
      step8_source_block_exact 55⟩
  · cases hb
    exact ⟨56, step8_source_pose_exact 56,
      step8_source_block_exact 56⟩
  · cases hb
    exact ⟨57, step8_source_pose_exact 57,
      step8_source_block_exact 57⟩
  · cases hb
    exact ⟨58, step8_source_pose_exact 58,
      step8_source_block_exact 58⟩
  · cases hb
    exact ⟨59, step8_source_pose_exact 59,
      step8_source_block_exact 59⟩
  · cases hb
    exact ⟨60, step8_source_pose_exact 60,
      step8_source_block_exact 60⟩
  · cases hb
    exact ⟨61, step8_source_pose_exact 61,
      step8_source_block_exact 61⟩
  · cases hb
    exact ⟨62, step8_source_pose_exact 62,
      step8_source_block_exact 62⟩
  · cases hb
    exact ⟨63, step8_source_pose_exact 63,
      step8_source_block_exact 63⟩

private theorem step8_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain1_1Ids,
    ∃ j, step8NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 64).map step8NeighborPoseIds =
      continuousScout898Domain1_1Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step8_neighbor_complete : ∀ pose ∈ continuousScout898Domain1_1Ids,
    ∃ j, (step8Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step8_neighbor_ids_complete pose member
  exact ⟨j,(step8_neighbor_pose_exact j).trans hj⟩

theorem step8_neighbor_unblocked : ∀ j, (step8Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step8LinkTargetIds : List (Fin poseCount) :=
  [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2773, 2773, 2773, 2773, 2773, 2773, 2773, 2773, 2773, 2783, 2783, 2783, 2783, 2783, 2783, 2783, 2791, 2791, 2791, 2791, 2791, 2791, 2791, 2799, 2799, 2799, 2799, 2804, 2804, 2804, 2808, 2810, 2812, 2814, 2816, 2818, 2820, 2822, 2824, 2826, 2828, 2830, 2832, 2834, 2836, 2838, 2840, 2842, 2844, 2846, 2848, 2850, 2852, 2854, 2856, 2858, 2860, 2862, 2864, 2866, 2868, 2870, 2872, 2874, 2876, 2878, 2880, 2882, 2884, 2886, 2888, 2890, 2892, 2894, 2896, 2898, 2900, 2902, 2904, 2906, 2906, 2906, 2910, 2910, 2910, 2910, 2910, 2910, 2910, 2918, 2918, 2918, 2918, 2918, 2918, 2925, 2925, 2925, 2925, 2925, 2925, 2932, 2932, 2932, 2932, 2932, 2932, 2932, 2932, 2932, 2942, 2942, 2942, 2942, 2942, 2942, 2942, 2942, 2942]

theorem step8_link_targets_mem :
    step8LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain0_9Ids)) = true := by
  decide +kernel

theorem step8_links_checked :
    ∀ piece ∈ step8Pieces, ∃ i ∈ step8Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain0_9Ids := by
  have exact_sources : step8Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step8Pieces := by rfl
  have exact_targets : step8Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step8LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step8LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step8_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
