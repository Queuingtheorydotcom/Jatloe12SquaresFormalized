import Compact.Cases.C898.CachedPairs.Step13Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step13_source_pose_exact (i : Fin 23) :
    (step13Sources i).pose = step13SourcePoseIds i := by fin_cases i <;> rfl

theorem step13_source_block_exact (i : Fin 23) :
    (step13Sources i).block = blockRows (step13SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step13_neighbor_pose_exact (j : Fin 63) :
    (step13Neighbors j).pose = step13NeighborPoseIds j := by fin_cases j <;> rfl

theorem step13_plans_checked : ∀ plan ∈ step13Plans, plan.Check complement := by
  decide +kernel

theorem step13_cover : StepCover continuousScout898Domain5_13Ids step13Pieces step13Plans := by
  decide +kernel

theorem step13_source_matches :
    ∀ plan ∈ step13Plans, ∀ block, plan.block = some block →
      ∃ i, (step13Sources i).pose = plan.source ∧
        (step13Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step13Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
    exact ⟨0, step13_source_pose_exact 0,
      step13_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step13_source_pose_exact 1,
      step13_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step13_source_pose_exact 2,
      step13_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step13_source_pose_exact 3,
      step13_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step13_source_pose_exact 4,
      step13_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step13_source_pose_exact 5,
      step13_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step13_source_pose_exact 6,
      step13_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step13_source_pose_exact 7,
      step13_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step13_source_pose_exact 8,
      step13_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step13_source_pose_exact 9,
      step13_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step13_source_pose_exact 10,
      step13_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step13_source_pose_exact 11,
      step13_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step13_source_pose_exact 12,
      step13_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step13_source_pose_exact 13,
      step13_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step13_source_pose_exact 14,
      step13_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step13_source_pose_exact 15,
      step13_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step13_source_pose_exact 16,
      step13_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step13_source_pose_exact 17,
      step13_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step13_source_pose_exact 18,
      step13_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step13_source_pose_exact 19,
      step13_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step13_source_pose_exact 20,
      step13_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step13_source_pose_exact 21,
      step13_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step13_source_pose_exact 22,
      step13_source_block_exact 22⟩

private theorem step13_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain7_7Ids,
    ∃ j, step13NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 63).map step13NeighborPoseIds =
      continuousScout898Domain7_7Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step13_neighbor_complete : ∀ pose ∈ continuousScout898Domain7_7Ids,
    ∃ j, (step13Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step13_neighbor_ids_complete pose member
  exact ⟨j,(step13_neighbor_pose_exact j).trans hj⟩

theorem step13_neighbor_unblocked : ∀ j, (step13Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step13LinkTargetIds : List (Fin poseCount) :=
  [3301, 3303, 3305, 3307, 3309, 3311, 3313, 3315]

theorem step13_link_targets_mem :
    step13LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain5_14Ids)) = true := by
  decide +kernel

theorem step13_links_checked :
    ∀ piece ∈ step13Pieces, ∃ i ∈ step13Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain5_14Ids := by
  have exact_sources : step13Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step13Pieces := by rfl
  have exact_targets : step13Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step13LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step13LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step13_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
