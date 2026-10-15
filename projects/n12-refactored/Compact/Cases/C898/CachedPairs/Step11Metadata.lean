import Compact.Cases.C898.CachedPairs.Step11Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step11_source_pose_exact (i : Fin 22) :
    (step11Sources i).pose = step11SourcePoseIds i := by fin_cases i <;> rfl

theorem step11_source_block_exact (i : Fin 22) :
    (step11Sources i).block = blockRows (step11SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step11_neighbor_pose_exact (j : Fin 61) :
    (step11Neighbors j).pose = step11NeighborPoseIds j := by fin_cases j <;> rfl

theorem step11_plans_checked : ∀ plan ∈ step11Plans, plan.Check complement := by
  decide +kernel

theorem step11_cover : StepCover continuousScout898Domain5_11Ids step11Pieces step11Plans := by
  decide +kernel

theorem step11_source_matches :
    ∀ plan ∈ step11Plans, ∀ block, plan.block = some block →
      ∃ i, (step11Sources i).pose = plan.source ∧
        (step11Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step11Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
    exact ⟨0, step11_source_pose_exact 0,
      step11_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step11_source_pose_exact 1,
      step11_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step11_source_pose_exact 2,
      step11_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step11_source_pose_exact 3,
      step11_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step11_source_pose_exact 4,
      step11_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step11_source_pose_exact 5,
      step11_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step11_source_pose_exact 6,
      step11_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step11_source_pose_exact 7,
      step11_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step11_source_pose_exact 8,
      step11_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step11_source_pose_exact 9,
      step11_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step11_source_pose_exact 10,
      step11_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step11_source_pose_exact 11,
      step11_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step11_source_pose_exact 12,
      step11_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step11_source_pose_exact 13,
      step11_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step11_source_pose_exact 14,
      step11_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step11_source_pose_exact 15,
      step11_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step11_source_pose_exact 16,
      step11_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step11_source_pose_exact 17,
      step11_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step11_source_pose_exact 18,
      step11_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step11_source_pose_exact 19,
      step11_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step11_source_pose_exact 20,
      step11_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step11_source_pose_exact 21,
      step11_source_block_exact 21⟩
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb

private theorem step11_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain0_9Ids,
    ∃ j, step11NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 61).map step11NeighborPoseIds =
      continuousScout898Domain0_9Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step11_neighbor_complete : ∀ pose ∈ continuousScout898Domain0_9Ids,
    ∃ j, (step11Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step11_neighbor_ids_complete pose member
  exact ⟨j,(step11_neighbor_pose_exact j).trans hj⟩

theorem step11_neighbor_unblocked : ∀ j, (step11Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step11LinkTargetIds : List (Fin poseCount) :=
  [3154, 3154, 3157, 3157, 3160, 3162, 3164, 3166, 3166, 3169, 3171, 3173, 3175, 3177, 3179, 3181, 3183, 3185, 3187, 3189, 3191, 3193, 3195, 3197, 3199, 3201, 3203, 3205, 3207, 3209, 3211, 3213, 3215, 3217, 3219, 3221, 3223, 3225, 3227, 3229, 3231, 3233, 3235, 3237, 3239, 3241, 3243, 3245, 3247, 3249, 3251, 3253]

theorem step11_link_targets_mem :
    step11LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain5_12Ids)) = true := by
  decide +kernel

theorem step11_links_checked :
    ∀ piece ∈ step11Pieces, ∃ i ∈ step11Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain5_12Ids := by
  have exact_sources : step11Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step11Pieces := by rfl
  have exact_targets : step11Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step11LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step11LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step11_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
