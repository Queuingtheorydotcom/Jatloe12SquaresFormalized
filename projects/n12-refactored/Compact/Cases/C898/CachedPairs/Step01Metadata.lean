import Compact.Cases.C898.CachedPairs.Step01Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step1_source_pose_exact (i : Fin 64) :
    (step1Sources i).pose = step1SourcePoseIds i := by fin_cases i <;> rfl

theorem step1_source_block_exact (i : Fin 64) :
    (step1Sources i).block = blockRows (step1SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step1_neighbor_pose_exact (j : Fin 64) :
    (step1Neighbors j).pose = step1NeighborPoseIds j := by fin_cases j <;> rfl

theorem step1_plans_checked : ∀ plan ∈ step1Plans, plan.Check complement := by
  decide +kernel

theorem step1_cover : StepCover continuousScout898Domain2_0Ids step1Pieces step1Plans := by
  decide +kernel

theorem step1_source_matches :
    ∀ plan ∈ step1Plans, ∀ block, plan.block = some block →
      ∃ i, (step1Sources i).pose = plan.source ∧
        (step1Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step1Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
    exact ⟨0, step1_source_pose_exact 0,
      step1_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step1_source_pose_exact 1,
      step1_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step1_source_pose_exact 2,
      step1_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step1_source_pose_exact 3,
      step1_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step1_source_pose_exact 4,
      step1_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step1_source_pose_exact 5,
      step1_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step1_source_pose_exact 6,
      step1_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step1_source_pose_exact 7,
      step1_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step1_source_pose_exact 8,
      step1_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step1_source_pose_exact 9,
      step1_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step1_source_pose_exact 10,
      step1_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step1_source_pose_exact 11,
      step1_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step1_source_pose_exact 12,
      step1_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step1_source_pose_exact 13,
      step1_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step1_source_pose_exact 14,
      step1_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step1_source_pose_exact 15,
      step1_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step1_source_pose_exact 16,
      step1_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step1_source_pose_exact 17,
      step1_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step1_source_pose_exact 18,
      step1_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step1_source_pose_exact 19,
      step1_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step1_source_pose_exact 20,
      step1_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step1_source_pose_exact 21,
      step1_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step1_source_pose_exact 22,
      step1_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step1_source_pose_exact 23,
      step1_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step1_source_pose_exact 24,
      step1_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step1_source_pose_exact 25,
      step1_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step1_source_pose_exact 26,
      step1_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step1_source_pose_exact 27,
      step1_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step1_source_pose_exact 28,
      step1_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step1_source_pose_exact 29,
      step1_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step1_source_pose_exact 30,
      step1_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step1_source_pose_exact 31,
      step1_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step1_source_pose_exact 32,
      step1_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step1_source_pose_exact 33,
      step1_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step1_source_pose_exact 34,
      step1_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step1_source_pose_exact 35,
      step1_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step1_source_pose_exact 36,
      step1_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step1_source_pose_exact 37,
      step1_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step1_source_pose_exact 38,
      step1_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step1_source_pose_exact 39,
      step1_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step1_source_pose_exact 40,
      step1_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step1_source_pose_exact 41,
      step1_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step1_source_pose_exact 42,
      step1_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step1_source_pose_exact 43,
      step1_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step1_source_pose_exact 44,
      step1_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step1_source_pose_exact 45,
      step1_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step1_source_pose_exact 46,
      step1_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step1_source_pose_exact 47,
      step1_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step1_source_pose_exact 48,
      step1_source_block_exact 48⟩
  · cases hb
    exact ⟨49, step1_source_pose_exact 49,
      step1_source_block_exact 49⟩
  · cases hb
    exact ⟨50, step1_source_pose_exact 50,
      step1_source_block_exact 50⟩
  · cases hb
    exact ⟨51, step1_source_pose_exact 51,
      step1_source_block_exact 51⟩
  · cases hb
    exact ⟨52, step1_source_pose_exact 52,
      step1_source_block_exact 52⟩
  · cases hb
    exact ⟨53, step1_source_pose_exact 53,
      step1_source_block_exact 53⟩
  · cases hb
    exact ⟨54, step1_source_pose_exact 54,
      step1_source_block_exact 54⟩
  · cases hb
    exact ⟨55, step1_source_pose_exact 55,
      step1_source_block_exact 55⟩
  · cases hb
    exact ⟨56, step1_source_pose_exact 56,
      step1_source_block_exact 56⟩
  · cases hb
    exact ⟨57, step1_source_pose_exact 57,
      step1_source_block_exact 57⟩
  · cases hb
    exact ⟨58, step1_source_pose_exact 58,
      step1_source_block_exact 58⟩
  · cases hb
    exact ⟨59, step1_source_pose_exact 59,
      step1_source_block_exact 59⟩
  · cases hb
    exact ⟨60, step1_source_pose_exact 60,
      step1_source_block_exact 60⟩
  · cases hb
    exact ⟨61, step1_source_pose_exact 61,
      step1_source_block_exact 61⟩
  · cases hb
    exact ⟨62, step1_source_pose_exact 62,
      step1_source_block_exact 62⟩
  · cases hb
    exact ⟨63, step1_source_pose_exact 63,
      step1_source_block_exact 63⟩

private theorem step1_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain10_0Ids,
    ∃ j, step1NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 64).map step1NeighborPoseIds =
      continuousScout898Domain10_0Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step1_neighbor_complete : ∀ pose ∈ continuousScout898Domain10_0Ids,
    ∃ j, (step1Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step1_neighbor_ids_complete pose member
  exact ⟨j,(step1_neighbor_pose_exact j).trans hj⟩

theorem step1_neighbor_unblocked : ∀ j, (step1Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step1LinkTargetIds : List (Fin poseCount) :=
  [1925, 1927, 1929, 1931, 1933, 1935, 1937, 1939, 1941, 1943, 1945, 1947, 1949, 1951, 1953, 1955, 1957, 1959, 1961, 1963, 1965, 1967, 1969, 1971, 1973, 1975, 1977, 1979, 1979, 1982, 1982, 1985, 1985, 1988, 1988, 1991, 1991, 1994, 1994, 1997, 1997, 2000, 2000, 2003, 2003, 2006, 2006, 2009, 2009, 2012, 2012, 2015, 2015, 2018, 2018, 2021, 2021, 2024, 2024, 2027, 2027, 2030, 2030, 2033, 2033, 2036, 2036, 2039, 2039, 2042, 2042, 2045, 2045, 2048, 2048, 2051, 2051, 2054, 2054, 2057, 2057, 2060, 2060, 2063, 2063, 2066, 2068, 2070, 2072, 2074, 2076, 2078, 2080]

theorem step1_link_targets_mem :
    step1LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain2_2Ids)) = true := by
  decide +kernel

theorem step1_links_checked :
    ∀ piece ∈ step1Pieces, ∃ i ∈ step1Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain2_2Ids := by
  have exact_sources : step1Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step1Pieces := by rfl
  have exact_targets : step1Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step1LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step1LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step1_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
