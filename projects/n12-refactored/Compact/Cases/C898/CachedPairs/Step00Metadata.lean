import Compact.Cases.C898.CachedPairs.Step00Data
import Compact.Cases.C898.CompactRelaxation.All

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem step0_source_pose_exact (i : Fin 50) :
    (step0Sources i).pose = step0SourcePoseIds i := by fin_cases i <;> rfl

theorem step0_source_block_exact (i : Fin 50) :
    (step0Sources i).block = blockRows (step0SourceBlockIds i) := by
  fin_cases i <;> rfl

theorem step0_neighbor_pose_exact (j : Fin 59) :
    (step0Neighbors j).pose = step0NeighborPoseIds j := by fin_cases j <;> rfl

theorem step0_plans_checked : ∀ plan ∈ step0Plans, plan.Check complement := by
  decide +kernel

theorem step0_cover : StepCover continuousScout898Domain1_0Ids step0Pieces step0Plans := by
  decide +kernel

theorem step0_source_matches :
    ∀ plan ∈ step0Plans, ∀ block, plan.block = some block →
      ∃ i, (step0Sources i).pose = plan.source ∧
        (step0Sources i).block = blockRows block := by
  intro plan member block hb
  simp only [step0Plans, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
    exact ⟨0, step0_source_pose_exact 0,
      step0_source_block_exact 0⟩
  · cases hb
    exact ⟨1, step0_source_pose_exact 1,
      step0_source_block_exact 1⟩
  · cases hb
    exact ⟨2, step0_source_pose_exact 2,
      step0_source_block_exact 2⟩
  · cases hb
    exact ⟨3, step0_source_pose_exact 3,
      step0_source_block_exact 3⟩
  · cases hb
    exact ⟨4, step0_source_pose_exact 4,
      step0_source_block_exact 4⟩
  · cases hb
    exact ⟨5, step0_source_pose_exact 5,
      step0_source_block_exact 5⟩
  · cases hb
    exact ⟨6, step0_source_pose_exact 6,
      step0_source_block_exact 6⟩
  · cases hb
    exact ⟨7, step0_source_pose_exact 7,
      step0_source_block_exact 7⟩
  · cases hb
    exact ⟨8, step0_source_pose_exact 8,
      step0_source_block_exact 8⟩
  · cases hb
    exact ⟨9, step0_source_pose_exact 9,
      step0_source_block_exact 9⟩
  · cases hb
    exact ⟨10, step0_source_pose_exact 10,
      step0_source_block_exact 10⟩
  · cases hb
    exact ⟨11, step0_source_pose_exact 11,
      step0_source_block_exact 11⟩
  · cases hb
    exact ⟨12, step0_source_pose_exact 12,
      step0_source_block_exact 12⟩
  · cases hb
    exact ⟨13, step0_source_pose_exact 13,
      step0_source_block_exact 13⟩
  · cases hb
    exact ⟨14, step0_source_pose_exact 14,
      step0_source_block_exact 14⟩
  · cases hb
    exact ⟨15, step0_source_pose_exact 15,
      step0_source_block_exact 15⟩
  · cases hb
    exact ⟨16, step0_source_pose_exact 16,
      step0_source_block_exact 16⟩
  · cases hb
    exact ⟨17, step0_source_pose_exact 17,
      step0_source_block_exact 17⟩
  · cases hb
    exact ⟨18, step0_source_pose_exact 18,
      step0_source_block_exact 18⟩
  · cases hb
    exact ⟨19, step0_source_pose_exact 19,
      step0_source_block_exact 19⟩
  · cases hb
    exact ⟨20, step0_source_pose_exact 20,
      step0_source_block_exact 20⟩
  · cases hb
    exact ⟨21, step0_source_pose_exact 21,
      step0_source_block_exact 21⟩
  · cases hb
    exact ⟨22, step0_source_pose_exact 22,
      step0_source_block_exact 22⟩
  · cases hb
    exact ⟨23, step0_source_pose_exact 23,
      step0_source_block_exact 23⟩
  · cases hb
    exact ⟨24, step0_source_pose_exact 24,
      step0_source_block_exact 24⟩
  · cases hb
    exact ⟨25, step0_source_pose_exact 25,
      step0_source_block_exact 25⟩
  · cases hb
    exact ⟨26, step0_source_pose_exact 26,
      step0_source_block_exact 26⟩
  · cases hb
    exact ⟨27, step0_source_pose_exact 27,
      step0_source_block_exact 27⟩
  · cases hb
    exact ⟨28, step0_source_pose_exact 28,
      step0_source_block_exact 28⟩
  · cases hb
    exact ⟨29, step0_source_pose_exact 29,
      step0_source_block_exact 29⟩
  · cases hb
    exact ⟨30, step0_source_pose_exact 30,
      step0_source_block_exact 30⟩
  · cases hb
    exact ⟨31, step0_source_pose_exact 31,
      step0_source_block_exact 31⟩
  · cases hb
    exact ⟨32, step0_source_pose_exact 32,
      step0_source_block_exact 32⟩
  · cases hb
    exact ⟨33, step0_source_pose_exact 33,
      step0_source_block_exact 33⟩
  · cases hb
    exact ⟨34, step0_source_pose_exact 34,
      step0_source_block_exact 34⟩
  · cases hb
    exact ⟨35, step0_source_pose_exact 35,
      step0_source_block_exact 35⟩
  · cases hb
    exact ⟨36, step0_source_pose_exact 36,
      step0_source_block_exact 36⟩
  · cases hb
    exact ⟨37, step0_source_pose_exact 37,
      step0_source_block_exact 37⟩
  · cases hb
    exact ⟨38, step0_source_pose_exact 38,
      step0_source_block_exact 38⟩
  · cases hb
    exact ⟨39, step0_source_pose_exact 39,
      step0_source_block_exact 39⟩
  · cases hb
    exact ⟨40, step0_source_pose_exact 40,
      step0_source_block_exact 40⟩
  · cases hb
    exact ⟨41, step0_source_pose_exact 41,
      step0_source_block_exact 41⟩
  · cases hb
    exact ⟨42, step0_source_pose_exact 42,
      step0_source_block_exact 42⟩
  · cases hb
    exact ⟨43, step0_source_pose_exact 43,
      step0_source_block_exact 43⟩
  · cases hb
    exact ⟨44, step0_source_pose_exact 44,
      step0_source_block_exact 44⟩
  · cases hb
    exact ⟨45, step0_source_pose_exact 45,
      step0_source_block_exact 45⟩
  · cases hb
    exact ⟨46, step0_source_pose_exact 46,
      step0_source_block_exact 46⟩
  · cases hb
    exact ⟨47, step0_source_pose_exact 47,
      step0_source_block_exact 47⟩
  · cases hb
    exact ⟨48, step0_source_pose_exact 48,
      step0_source_block_exact 48⟩
  · cases hb
    exact ⟨49, step0_source_pose_exact 49,
      step0_source_block_exact 49⟩
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb
  · cases hb

private theorem step0_neighbor_ids_complete : ∀ pose ∈ continuousScout898Domain8_0Ids,
    ∃ j, step0NeighborPoseIds j = pose := by
  have exact_ids : (List.finRange 59).map step0NeighborPoseIds =
      continuousScout898Domain8_0Ids := by rfl
  intro pose member
  rw [← exact_ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, hj⟩

theorem step0_neighbor_complete : ∀ pose ∈ continuousScout898Domain8_0Ids,
    ∃ j, (step0Neighbors j).pose = pose := by
  intro pose member
  obtain ⟨j,hj⟩ := step0_neighbor_ids_complete pose member
  exact ⟨j,(step0_neighbor_pose_exact j).trans hj⟩

theorem step0_neighbor_unblocked : ∀ j, (step0Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl

def step0LinkTargetIds : List (Fin poseCount) :=
  [1751, 1753, 1755, 1757, 1759, 1761, 1763, 1763, 1766, 1766, 1766, 1770, 1770, 1770, 1774, 1774, 1774, 1774, 1779, 1779, 1779, 1779, 1784, 1784, 1784, 1784, 1789, 1789, 1789, 1789, 1794, 1794, 1794, 1798, 1798, 1801, 1803, 1805, 1807, 1809, 1811, 1811, 1814, 1814, 1814, 1818, 1818, 1821, 1821, 1824, 1824, 1827, 1827, 1830, 1830, 1833, 1833, 1836, 1836, 1839, 1839, 1842, 1842, 1845, 1845, 1848, 1848, 1851, 1851, 1854, 1854, 1854, 1858, 1858, 1858, 1862, 1862, 1862, 1866, 1866, 1866, 1870, 1870, 1870, 1874, 1874, 1877, 1879, 1881, 1883, 1885, 1887, 1889, 1891, 1893, 1895, 1897, 1899, 1901, 1903, 1905, 1907, 1909, 1911, 1913, 1915, 1917, 1919, 1921, 1923]

theorem step0_link_targets_mem :
    step0LinkTargetIds.all (fun target => decide (target ∈ continuousScout898Domain1_1Ids)) = true := by
  decide +kernel

theorem step0_links_checked :
    ∀ piece ∈ step0Pieces, ∃ i ∈ step0Links,
      (C898CompactRelaxation.links i).source = piece ∧
      (C898CompactRelaxation.links i).target ∈ continuousScout898Domain1_1Ids := by
  have exact_sources : step0Links.map (fun i => (C898CompactRelaxation.links i).source) =
      step0Pieces := by rfl
  have exact_targets : step0Links.map (fun i => (C898CompactRelaxation.links i).target) =
      step0LinkTargetIds := by rfl
  intro piece member
  rw [← exact_sources] at member
  obtain ⟨i, hi, he⟩ := List.mem_map.mp member
  have target_member : (C898CompactRelaxation.links i).target ∈ step0LinkTargetIds := by
    rw [← exact_targets]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact ⟨i, hi, he, of_decide_eq_true (List.all_eq_true.mp step0_link_targets_mem _ target_member)⟩

end
end N12Compact.C898Cached.AllPairs
