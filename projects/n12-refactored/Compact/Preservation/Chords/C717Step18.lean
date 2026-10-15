import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C717

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C717Step18
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C717

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (107015641/50000000)
def hi : ℚ := (216034103/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (4740,radius64,radius64_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (4741,radius186,radius186_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (4742,radius187,radius187_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (4743,radius188,radius188_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (4744,radius189,radius189_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (4745,radius190,radius190_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (4746,radius191,radius191_checked,[.single 7, .single 4])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout717Domain3_17Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (5643,radius64,radius64_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (5644,radius65,radius65_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (5645,radius74,radius74_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (5646,radius75,radius75_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (5647,radius76,radius76_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (5648,radius77,radius77_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (5649,radius78,radius78_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (5650,radius79,radius79_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (5651,radius80,radius80_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (5652,radius190,radius190_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (5653,radius191,radius191_checked,[.single 8, .single 3])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout717Domain7_11Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (5889,radius64,radius64_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (5890,radius65,radius65_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (5891,radius66,radius66_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (5892,radius67,radius67_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (5893,radius68,radius68_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (5894,radius69,radius69_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (5895,radius70,radius70_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (5896,radius71,radius71_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (5897,radius72,radius72_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (5898,radius73,radius73_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (5899,radius74,radius74_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (5900,radius75,radius75_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (5901,radius76,radius76_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (5902,radius77,radius77_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (5903,radius78,radius78_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (5904,radius79,radius79_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (5905,radius187,radius187_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (5906,radius188,radius188_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (5907,radius189,radius189_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (5908,radius190,radius190_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (5909,radius191,radius191_checked,[.single 7, .single 3])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout717Domain9_13Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (5259,radius72,radius72_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (5260,radius73,radius73_checked,chord_close%(⟨[0,7],[(1,0),(200,7)]⟩),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (5261,radius74,radius74_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (5262,radius75,radius75_checked,chord_close%(⟨[0,8],[(20,0),(1,8)]⟩),chord_close%(⟨[0,4],[(5,0),(2,4)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (5263,radius76,radius76_checked,chord_close%(⟨[0,8],[(128,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (5264,radius77,radius77_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (5265,radius78,radius78_checked,chord_close%(⟨[0,8],[(40,0),(1,8)]⟩),chord_close%(⟨[0,4],[(5,0),(2,4)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (5266,radius79,radius79_checked,chord_close%(⟨[0,8],[(40,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (5267,radius80,radius80_checked,chord_close%(⟨[0,8],[(4,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (5268,radius81,radius81_checked,chord_close%(⟨[0,8],[(2,0),(5,8)]⟩),chord_close%(⟨[0,4],[(1,0),(20,4)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (5269,radius82,radius82_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(64,4)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (5270,radius83,radius83_checked,chord_close%(⟨[0,8],[(1,0),(2,8)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (5271,radius84,radius84_checked,chord_close%(⟨[0,8],[(1,0),(8,8)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (5272,radius85,radius85_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (5273,radius86,radius86_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (5274,radius87,radius87_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout717Domain6_18Ids := by rfl
def outputIds : List (Fin poseCount) := []
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout717Domain6_19Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout717Domain6_19Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout717Domain6_18 (q 0))
    (h0 : OrientedPoseCovered continuousScout717Domain3_17 (q 1))
    (h1 : OrientedPoseCovered continuousScout717Domain7_11 (q 2))
    (h2 : OrientedPoseCovered continuousScout717Domain9_13 (q 3))
    : OrientedPoseCovered continuousScout717Domain6_19 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout717Domain6_18Ids continuousScout717Domain6_19Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain3_17Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain7_11Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain9_13Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![768,16,3072,8192]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768)))
    (h0 : OrientedPoseCovered continuousScout717Domain3_17 (p.square (ownerIndex p 16)))
    (h1 : OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)))
    (h2 : OrientedPoseCovered continuousScout717Domain9_13 (p.square (ownerIndex p 8192)))
    : OrientedPoseCovered continuousScout717Domain6_19 (p.square (ownerIndex p 768)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout717Domain6_18 continuousScout717Domain6_19
    ![continuousScout717Domain3_17,continuousScout717Domain7_11,continuousScout717Domain9_13]
    (fun q side box disjoint source neighbors =>
      sound q side box disjoint source (neighbors 0) (neighbors 1) (neighbors 2))
    p family_exact incoming
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms packing_sound

#print axioms sound

end
end N12Compact.Preservation.Chords.C717Step18
