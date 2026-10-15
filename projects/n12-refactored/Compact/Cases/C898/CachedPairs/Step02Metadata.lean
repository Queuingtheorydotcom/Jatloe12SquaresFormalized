import Compact.Cases.C898.CachedPairs.Step02Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step2_source_pose_exact (i : Fin 47) :
    (step2Sources i).pose = step2SourcePoseIds i := by fin_cases i <;> rfl

theorem step2_source_block_exact (i : Fin 47) :
    (step2Sources i).block = blockRows (step2SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step2_neighbor_pose_exact (j : Fin 59) :
    (step2Neighbors j).pose = step2NeighborPoseIds j := by fin_cases j <;> rfl

theorem step2_plans_checked : ∀ plan ∈ step2Plans, plan.Check complement := by
  decide +kernel

theorem step2_cover : StepCover continuousScout898Domain3_0Ids step2Pieces step2Plans := by
  decide +kernel

theorem step2_source_matches :
    ∀ plan ∈ step2Plans, ∀ block, plan.block = some block →
      ∃ i, (step2Sources i).pose = plan.source ∧
        (step2Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step2Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step2_source_pose_exact 0,
      step2_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step2_source_pose_exact 1,
      step2_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step2_source_pose_exact 2,
      step2_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step2_source_pose_exact 3,
      step2_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step2_source_pose_exact 4,
      step2_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step2_source_pose_exact 5,
      step2_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step2_source_pose_exact 6,
      step2_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step2_source_pose_exact 7,
      step2_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step2_source_pose_exact 8,
      step2_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step2_source_pose_exact 9,
      step2_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step2_source_pose_exact 10,
      step2_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step2_source_pose_exact 11,
      step2_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step2_source_pose_exact 12,
      step2_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step2_source_pose_exact 13,
      step2_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step2_source_pose_exact 14,
      step2_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step2_source_pose_exact 15,
      step2_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step2_source_pose_exact 16,
      step2_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step2_source_pose_exact 17,
      step2_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step2_source_pose_exact 18,
      step2_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step2_source_pose_exact 19,
      step2_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step2_source_pose_exact 20,
      step2_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step2_source_pose_exact 21,
      step2_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step2_source_pose_exact 22,
      step2_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step2_source_pose_exact 23,
      step2_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step2_source_pose_exact 24,
      step2_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step2_source_pose_exact 25,
      step2_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step2_source_pose_exact 26,
      step2_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step2_source_pose_exact 27,
      step2_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step2_source_pose_exact 28,
      step2_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step2_source_pose_exact 29,
      step2_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step2_source_pose_exact 30,
      step2_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step2_source_pose_exact 31,
      step2_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step2_source_pose_exact 32,
      step2_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step2_source_pose_exact 33,
      step2_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step2_source_pose_exact 34,
      step2_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step2_source_pose_exact 35,
      step2_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step2_source_pose_exact 36,
      step2_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step2_source_pose_exact 37,
      step2_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step2_source_pose_exact 38,
      step2_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step2_source_pose_exact 39,
      step2_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step2_source_pose_exact 40,
      step2_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step2_source_pose_exact 41,
      step2_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step2_source_pose_exact 42,
      step2_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step2_source_pose_exact 43,
      step2_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step2_source_pose_exact 44,
      step2_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step2_source_pose_exact 45,
      step2_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step2_source_pose_exact 46,
      step2_source_block_exact 46⟩
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

private theorem step2_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain11_0Ids,
    ∃ j, step2NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 59).map step2NeighborPoseIds =
      continuousScout898Domain11_0Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step2_neighbor_complete : ∀ pose ∈ continuousScout898Domain11_0Ids,
    ∃ j, (step2Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step2_neighbor_ids_complete pose member
  exact ⟨j,(step2_neighbor_pose_exact j).trans hj⟩

theorem step2_neighbor_unblocked : ∀ j, (step2Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step2LinkTargetIds : List (Fin poseCount) :=
  [2082, 2084, 2086, 2088, 2090, 2092, 2094, 2096, 2096, 2099, 2099, 2099, 2099, 2104, 2104, 2104, 2104, 2104, 2110, 2110, 2110, 2110, 2110, 2116, 2116, 2116, 2116, 2121, 2123, 2125, 2127, 2129, 2131, 2133, 2135, 2135, 2135, 2139, 2139, 2142, 2142, 2145, 2145, 2148, 2150, 2150, 2153, 2153, 2156, 2158, 2158, 2161, 2161, 2164, 2164, 2167, 2167, 2170, 2170, 2173, 2173, 2176, 2176, 2176, 2180, 2180, 2183, 2183, 2183, 2187, 2187, 2190, 2190, 2193, 2193, 2196, 2196, 2199, 2199, 2202, 2202, 2205, 2205, 2208, 2208, 2211, 2211, 2214, 2214, 2217, 2217, 2220, 2220, 2223, 2223, 2226, 2226, 2229, 2229, 2232, 2232, 2235, 2235, 2238, 2240, 2242, 2244, 2246, 2248, 2250, 2252, 2254, 2256, 2258]

theorem step2_link_targets_mem :
    step2LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain3_3Ids)) = true := by
  decide +kernel

theorem step2_links_checked :
    ∀ piece ∈ step2Pieces, ∃ i ∈ step2Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain3_3Ids := by
  have exact_sources : step2Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step2Pieces := by rfl
  have exact_targets : step2Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step2LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step2LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step2_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
