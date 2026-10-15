import Compact.Cases.C898.CachedPairs.Step05Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step5_source_pose_exact (i : Fin 51) :
    (step5Sources i).pose = step5SourcePoseIds i := by fin_cases i <;> rfl

theorem step5_source_block_exact (i : Fin 51) :
    (step5Sources i).block = blockRows (step5SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step5_neighbor_pose_exact (j : Fin 12) :
    (step5Neighbors j).pose = step5NeighborPoseIds j := by fin_cases j <;> rfl

theorem step5_plans_checked : ∀ plan ∈ step5Plans, plan.Check complement := by
  decide +kernel

theorem step5_cover : StepCover continuousScout898Domain7_0Ids step5Pieces step5Plans := by
  decide +kernel

theorem step5_source_matches :
    ∀ plan ∈ step5Plans, ∀ block, plan.block = some block →
      ∃ i, (step5Sources i).pose = plan.source ∧
        (step5Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step5Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    exact ⟨0, step5_source_pose_exact 0,
      step5_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step5_source_pose_exact 1,
      step5_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step5_source_pose_exact 2,
      step5_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step5_source_pose_exact 3,
      step5_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step5_source_pose_exact 4,
      step5_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step5_source_pose_exact 5,
      step5_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step5_source_pose_exact 6,
      step5_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step5_source_pose_exact 7,
      step5_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step5_source_pose_exact 8,
      step5_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step5_source_pose_exact 9,
      step5_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step5_source_pose_exact 10,
      step5_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step5_source_pose_exact 11,
      step5_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step5_source_pose_exact 12,
      step5_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step5_source_pose_exact 13,
      step5_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step5_source_pose_exact 14,
      step5_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step5_source_pose_exact 15,
      step5_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step5_source_pose_exact 16,
      step5_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step5_source_pose_exact 17,
      step5_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step5_source_pose_exact 18,
      step5_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step5_source_pose_exact 19,
      step5_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step5_source_pose_exact 20,
      step5_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step5_source_pose_exact 21,
      step5_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step5_source_pose_exact 22,
      step5_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step5_source_pose_exact 23,
      step5_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step5_source_pose_exact 24,
      step5_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step5_source_pose_exact 25,
      step5_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step5_source_pose_exact 26,
      step5_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step5_source_pose_exact 27,
      step5_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step5_source_pose_exact 28,
      step5_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step5_source_pose_exact 29,
      step5_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step5_source_pose_exact 30,
      step5_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step5_source_pose_exact 31,
      step5_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step5_source_pose_exact 32,
      step5_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step5_source_pose_exact 33,
      step5_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step5_source_pose_exact 34,
      step5_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step5_source_pose_exact 35,
      step5_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step5_source_pose_exact 36,
      step5_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step5_source_pose_exact 37,
      step5_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step5_source_pose_exact 38,
      step5_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step5_source_pose_exact 39,
      step5_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step5_source_pose_exact 40,
      step5_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step5_source_pose_exact 41,
      step5_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step5_source_pose_exact 42,
      step5_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step5_source_pose_exact 43,
      step5_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step5_source_pose_exact 44,
      step5_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step5_source_pose_exact 45,
      step5_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step5_source_pose_exact 46,
      step5_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step5_source_pose_exact 47,
      step5_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step5_source_pose_exact 48,
      step5_source_block_exact 48⟩
  · cases hb
    exact ⟨49, step5_source_pose_exact 49,
      step5_source_block_exact 49⟩
  · cases hb
    exact ⟨50, step5_source_pose_exact 50,
      step5_source_block_exact 50⟩
  · cases hb

private theorem step5_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain6_5Ids,
    ∃ j, step5NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 12).map step5NeighborPoseIds =
      continuousScout898Domain6_5Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step5_neighbor_complete : ∀ pose ∈ continuousScout898Domain6_5Ids,
    ∃ j, (step5Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step5_neighbor_ids_complete pose member
  exact ⟨j,(step5_neighbor_pose_exact j).trans hj⟩

theorem step5_neighbor_unblocked : ∀ j, (step5Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step5LinkTargetIds : List (Fin poseCount) :=
  [2313, 2315, 2317, 2319, 2321, 2323, 2325, 2327, 2329, 2331, 2333, 2335, 2337, 2339, 2341, 2343, 2345, 2347, 2349, 2351, 2353, 2355, 2357, 2359, 2361, 2363, 2365, 2365, 2368, 2368, 2371, 2371, 2374, 2376, 2378, 2380, 2382, 2384, 2386, 2388, 2390, 2392, 2394, 2396, 2398, 2398, 2401, 2401, 2404, 2404, 2407, 2407, 2410, 2410, 2413, 2413, 2416, 2416, 2419, 2419, 2422, 2422, 2425, 2425, 2428, 2428, 2431, 2431, 2434, 2434, 2437, 2437, 2440, 2442, 2444, 2446, 2448, 2450, 2452, 2454]

theorem step5_link_targets_mem :
    step5LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain7_6Ids)) = true := by
  decide +kernel

theorem step5_links_checked :
    ∀ piece ∈ step5Pieces, ∃ i ∈ step5Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain7_6Ids := by
  have exact_sources : step5Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step5Pieces := by rfl
  have exact_targets : step5Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step5LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step5LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step5_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
