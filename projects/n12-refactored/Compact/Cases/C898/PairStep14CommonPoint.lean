import Compact.Cases.C898.PairStep14CachedContexts
import Compact.Cases.C898.CachedCommonPoint
import Compact.Cases.C898.CommonPairGroups
import Compact.Cases.C898.SharedDomains
import Compact.Core.BoundaryFanSyntax
import Compact.Core.KernelMatrix
import S12.OrientedCoverage

/-! A single common point closes the whole original terminal stage. Every
one of the eight incoming source poses and fifty-three neighbor poses contains
this point, under its original real-square realization. No pruning, pairwise
axis matrix, or outward-relaxation premise is required. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.TerminalCommon
open C898Shared S12 CommonGroups
noncomputable section

def point : CommonPoint.Point := ⟨10079, 4914, 5000⟩

def rawSources : Fin 8 → RawSupportFan.Context := ![
  terminalRawContext0, terminalRawContext54, terminalRawContext55, terminalRawContext56, terminalRawContext57, terminalRawContext58, terminalRawContext59, terminalRawContext60]

def rawNeighbors : Fin 53 → RawSupportFan.Context := ![
  terminalRawContext1, terminalRawContext2, terminalRawContext3, terminalRawContext4, terminalRawContext5, terminalRawContext6, terminalRawContext7, terminalRawContext8, terminalRawContext9, terminalRawContext10, terminalRawContext11, terminalRawContext12, terminalRawContext13, terminalRawContext14, terminalRawContext15, terminalRawContext16, terminalRawContext17, terminalRawContext18, terminalRawContext19, terminalRawContext20, terminalRawContext21, terminalRawContext22, terminalRawContext23, terminalRawContext24, terminalRawContext25, terminalRawContext26, terminalRawContext27, terminalRawContext28, terminalRawContext29, terminalRawContext30, terminalRawContext31, terminalRawContext32, terminalRawContext33, terminalRawContext34, terminalRawContext35, terminalRawContext36, terminalRawContext37, terminalRawContext38, terminalRawContext39, terminalRawContext40, terminalRawContext41, terminalRawContext42, terminalRawContext43, terminalRawContext44, terminalRawContext45, terminalRawContext46, terminalRawContext47, terminalRawContext48, terminalRawContext49, terminalRawContext50, terminalRawContext51, terminalRawContext52, terminalRawContext53]

theorem rawSources_exact (i : Fin 8) :
    rawSources i = (cachedStep14Source i).context.numeric := by
  fin_cases i
  · exact terminalRawContext0_exact
  · exact terminalRawContext54_exact
  · exact terminalRawContext55_exact
  · exact terminalRawContext56_exact
  · exact terminalRawContext57_exact
  · exact terminalRawContext58_exact
  · exact terminalRawContext59_exact
  · exact terminalRawContext60_exact

theorem rawNeighbors_exact (j : Fin 53) :
    rawNeighbors j = (cachedStep14Neighbor j).context.numeric := by
  fin_cases j
  · exact terminalRawContext1_exact
  · exact terminalRawContext2_exact
  · exact terminalRawContext3_exact
  · exact terminalRawContext4_exact
  · exact terminalRawContext5_exact
  · exact terminalRawContext6_exact
  · exact terminalRawContext7_exact
  · exact terminalRawContext8_exact
  · exact terminalRawContext9_exact
  · exact terminalRawContext10_exact
  · exact terminalRawContext11_exact
  · exact terminalRawContext12_exact
  · exact terminalRawContext13_exact
  · exact terminalRawContext14_exact
  · exact terminalRawContext15_exact
  · exact terminalRawContext16_exact
  · exact terminalRawContext17_exact
  · exact terminalRawContext18_exact
  · exact terminalRawContext19_exact
  · exact terminalRawContext20_exact
  · exact terminalRawContext21_exact
  · exact terminalRawContext22_exact
  · exact terminalRawContext23_exact
  · exact terminalRawContext24_exact
  · exact terminalRawContext25_exact
  · exact terminalRawContext26_exact
  · exact terminalRawContext27_exact
  · exact terminalRawContext28_exact
  · exact terminalRawContext29_exact
  · exact terminalRawContext30_exact
  · exact terminalRawContext31_exact
  · exact terminalRawContext32_exact
  · exact terminalRawContext33_exact
  · exact terminalRawContext34_exact
  · exact terminalRawContext35_exact
  · exact terminalRawContext36_exact
  · exact terminalRawContext37_exact
  · exact terminalRawContext38_exact
  · exact terminalRawContext39_exact
  · exact terminalRawContext40_exact
  · exact terminalRawContext41_exact
  · exact terminalRawContext42_exact
  · exact terminalRawContext43_exact
  · exact terminalRawContext44_exact
  · exact terminalRawContext45_exact
  · exact terminalRawContext46_exact
  · exact terminalRawContext47_exact
  · exact terminalRawContext48_exact
  · exact terminalRawContext49_exact
  · exact terminalRawContext50_exact
  · exact terminalRawContext51_exact
  · exact terminalRawContext52_exact
  · exact terminalRawContext53_exact

def sourceAngles (i : Fin 8) : Fin 64 := ⟨11 + i.val, by omega⟩

def neighborAngles (j : Fin 53) : Fin 64 :=
  ⟨if j.val < 20 then j.val else j.val + 11, by split <;> omega⟩

kernel_matrix source_checked : 8 × 1 => (fun i _ =>
  CommonPoint.check (rawSources i) (ownKeys (sourceAngles i)) point = true)

kernel_matrix neighbor_checked : 53 × 1 => (fun j _ =>
  CommonPoint.check (rawNeighbors j) (ownKeys (neighborAngles j)) point = true)

def sourcePoseIds : Fin 8 → Fin poseCount :=
  ![3301, 3303, 3305, 3307, 3309, 3311, 3313, 3315]

def neighborPoseIds : Fin 53 → Fin poseCount :=
  ![2629, 2631, 2633, 2636, 2639, 2642, 2645, 2648, 2651, 2654, 2657, 2660,
    2663, 2666, 2669, 2671, 2673, 2675, 2677, 2679, 2681, 2683, 2685, 2687,
    2689, 2691, 2693, 2695, 2697, 2699, 2701, 2703, 2705, 2708, 2711, 2714,
    2717, 2720, 2723, 2726, 2729, 2732, 2735, 2738, 2741, 2744, 2747, 2750,
    2752, 2754, 2756, 2758, 2760]

theorem source_pose_exact (i : Fin 8) :
    (cachedStep14Source i).pose = sourcePoseIds i := by fin_cases i <;> rfl

theorem neighbor_pose_exact (j : Fin 53) :
    (cachedStep14Neighbor j).pose = neighborPoseIds j := by fin_cases j <;> rfl

theorem source_block_empty (i : Fin 8) : (cachedStep14Source i).block = [] := by
  fin_cases i <;> rfl

theorem neighbor_block_empty (j : Fin 53) : (cachedStep14Neighbor j).block = [] := by
  fin_cases j <;> rfl

theorem sources_complete : ∀ pose ∈ continuousScout898Domain5_14Ids,
    ∃ i, (cachedStep14Source i).pose = pose := by
  have ids : (List.finRange 8).map sourcePoseIds = continuousScout898Domain5_14Ids := rfl
  intro pose member
  rw [← ids] at member
  obtain ⟨i, _, hi⟩ := List.mem_map.mp member
  exact ⟨i, (source_pose_exact i).trans hi⟩

theorem neighbors_complete : ∀ pose ∈ continuousScout898Domain9_8Ids,
    ∃ j, (cachedStep14Neighbor j).pose = pose := by
  have ids : (List.finRange 53).map neighborPoseIds = continuousScout898Domain9_8Ids := rfl
  intro pose member
  rw [← ids] at member
  obtain ⟨j, _, hj⟩ := List.mem_map.mp member
  exact ⟨j, (neighbor_pose_exact j).trans hj⟩

theorem pairStep14_common_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_14 q)
    (ht : OrientedPoseCovered continuousScout898Domain9_8 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_15 q := by
  obtain ⟨source, member, realizes⟩ := hq
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, hi⟩ := sources_complete source in_sources
  obtain ⟨neighbor, member, neighbor_realizes⟩ := ht
  obtain ⟨neighbor, in_neighbors, rfl⟩ := List.mem_map.mp member
  obtain ⟨j, hj⟩ := neighbors_complete neighbor in_neighbors
  have source_inside := (cachedStep14Source i).point_sound (rawSources i) (rawSources_exact i)
    (ownKeys (sourceAngles i)) point (source_checked i 0) q
    (by simpa only [hi] using realizes.1)
    (by simp only [source_block_empty i, List.not_mem_nil, false_implies, forall_const])
  have neighbor_inside := (cachedStep14Neighbor j).point_sound (rawNeighbors j) (rawNeighbors_exact j)
    (ownKeys (neighborAngles j)) point (neighbor_checked j 0) t
    (by simpa only [hj] using neighbor_realizes.1)
    (by simp only [neighbor_block_empty j, List.not_mem_nil, false_implies, forall_const])
  exact (disjoint point.value.1 point.value.2 ⟨source_inside, neighbor_inside⟩).elim

#print axioms pairStep14_common_sound

end
end N12Compact.C898Cached.TerminalCommon
