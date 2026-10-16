import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C701

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C701Step23
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C701

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (73412811/50000000)
def hi : ℚ := (22456181/12500000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (686,radius0,radius0_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (687,radius1,radius1_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (688,radius2,radius2_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (689,radius3,radius3_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (690,radius4,radius4_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (691,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (692,radius61,radius61_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (693,radius62,radius62_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (694,radius63,radius63_checked,[.single 0, .single 4])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout701Domain1_22Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (1390,radius0,radius0_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (1391,radius1,radius1_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (1392,radius2,radius2_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (1393,radius3,radius3_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (1394,radius4,radius4_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (1395,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (1396,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (1397,radius61,radius61_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (1398,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (1399,radius63,radius63_checked,[.single 2, .single 6])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout701Domain6_13Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (262,radius0,radius0_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (263,radius1,radius1_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (264,radius2,radius2_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (265,radius3,radius3_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (266,radius4,radius4_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (267,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (268,radius6,radius6_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (269,radius7,radius7_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (270,radius8,radius8_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (271,radius9,radius9_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (272,radius10,radius10_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (273,radius11,radius11_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (274,radius12,radius12_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (275,radius13,radius13_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (276,radius14,radius14_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (277,radius15,radius15_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (278,radius16,radius16_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (279,radius17,radius17_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (280,radius18,radius18_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (281,radius19,radius19_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (282,radius20,radius20_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (283,radius21,radius21_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (284,radius34,radius34_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (285,radius35,radius35_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (286,radius36,radius36_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (287,radius37,radius37_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (288,radius38,radius38_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (289,radius39,radius39_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (290,radius40,radius40_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (291,radius41,radius41_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (292,radius42,radius42_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (293,radius43,radius43_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (294,radius44,radius44_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (295,radius45,radius45_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (296,radius46,radius46_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (297,radius47,radius47_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (298,radius48,radius48_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (299,radius49,radius49_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (300,radius50,radius50_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (301,radius51,radius51_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (302,radius52,radius52_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (303,radius53,radius53_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (304,radius54,radius54_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (305,radius55,radius55_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (306,radius56,radius56_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (307,radius57,radius57_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (308,radius58,radius58_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (309,radius59,radius59_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (310,radius60,radius60_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (311,radius61,radius61_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (312,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (313,radius63,radius63_checked,[.single 1, .single 4])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout701Domain10_6Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (1453,radius0,radius0_checked,chord_close%(⟨[0,2],[(128,0),(1,2)]⟩),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (1454,radius1,radius1_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,5],[(1,0),(20,5)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (1455,radius2,radius2_checked,chord_close%(⟨[0,2],[(16,0),(5,2)]⟩),chord_close%(⟨[0,6],[(1,0),(40,6)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (1456,radius3,radius3_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,6],[(1,0),(25,6)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (1457,radius4,radius4_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (1458,radius15,radius15_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(1466,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (1459,radius16,radius16_checked,chord_close%(⟨[0,2],[(40,0),(1,2)]⟩),chord_keep%(1467,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (1460,radius17,radius17_checked,chord_close%(⟨[0,2],[(32,0),(5,2)]⟩),chord_keep%(1468,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (1461,radius18,radius18_checked,chord_close%(⟨[0,2],[(5,0),(4,2)]⟩),chord_keep%(1469,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (1462,radius19,radius19_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1470,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (1463,radius26,radius26_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1471,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (1464,radius27,radius27_checked,chord_close%(⟨[0,2],[(1,0),(40,2)]⟩),chord_keep%(1472,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (1465,radius63,radius63_checked,chord_close%(⟨[0,1],[(20,0),(1,1)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout701Domain7_14Ids := by rfl
def outputIds : List (Fin poseCount) := [1466,1467,1468,1469,1470,1471,1472]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout701Domain7_24Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout701Domain7_24Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout701Domain7_14 (q 0))
    (h0 : OrientedPoseCovered continuousScout701Domain1_22 (q 1))
    (h1 : OrientedPoseCovered continuousScout701Domain6_13 (q 2))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (q 3))
    : OrientedPoseCovered continuousScout701Domain7_24 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout701Domain7_14Ids continuousScout701Domain7_24Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain1_22Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain6_13Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain10_6Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![1536,2,256,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout701Domain7_14 (p.square (ownerIndex p 1536)))
    (h0 : OrientedPoseCovered continuousScout701Domain1_22 (p.square (ownerIndex p 2)))
    (h1 : OrientedPoseCovered continuousScout701Domain6_13 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout701Domain7_24 (p.square (ownerIndex p 1536)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout701Domain7_14 continuousScout701Domain7_24
    ![continuousScout701Domain1_22,continuousScout701Domain6_13,continuousScout701Domain10_6]
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
end N12Compact.Preservation.Chords.C701Step23
