import Compact.Completion.OtherCases.C1089.LastSectorNorthwestInput
import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.OtherCases.CrossedElbow
import Compact.Completion.C1092.MixedSpan

/-! The actual northwest ordinary pair in C1089-LAST-SECTOR-REDUCTION
sections 4--5. Every point used in a duplicate or corner obstruction has its
literal actual source. No component label or orientation of Q7 is assumed.
The underlying core/covering entrance remains an explicit input. This is
uncompiled source, not an original-family exclusion. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest
open S12 S12Pilot
set_option Elab.async false

theorem northwest_f3 (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (8/5) 3 := by
  by_contra missingF3
  have f5 := (f_alternatives q h).resolve_left missingF3
  by_cases g3 : (q 7).Inside (87/50) 2
  · have inward := CommonCases.InwardPoint.point_original (pullY (pullX (q 7))) (h.side 7)
      (by norm_num [inside_pullY,inside_pullX]; exact h.northwestMarker)
      (by norm_num [inside_pullY,inside_pullX]; exact f5)
      (by norm_num [inside_pullY,inside_pullX]; exact g3)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact missingF3)
    norm_num [inside_pullY,inside_pullX] at inward
    have missingG3 : ¬(q 4).Inside (87/50) 2 :=
      fun own => h.apart 4 7 (by decide) _ _ ⟨own,g3⟩
    have corner := InnerCornerObstruction.inward_corner_excluded_original (q 4) (h.side 4)
      h.southwestMarker h.absentMarker
      (fun own => h.apart 4 0 (by decide) _ _ ⟨own,h.singletonNear⟩)
      (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
      (27/50) (101/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      missingG3 (by
        norm_num
        exact fun own => h.apart 4 7 (by decide) _ _ ⟨own,inward⟩)
    exact h.apart 4 7 (by decide) _ _ ⟨(outward_points q h corner missingG3).1,inward⟩
  · have g4 := (g_alternatives q h).resolve_left g3
    have points := ElbowPoint.points_original (pullSwap (q 7)) (h.side 7)
      (by norm_num [inside_pullSwap]; exact h.northwestMarker)
      (by norm_num [inside_pullSwap]; exact f5)
      (by norm_num [inside_pullSwap]; exact g4)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullSwap]; exact missingF3)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,h.topMarker⟩)
    norm_num [inside_pullSwap] at points
    have missingG3 : ¬(q 4).Inside (87/50) 2 := by
      intro own
      exact CrossedElbow.impossible_original (pullX (q 4)) (4/5) (h.side 4)
        (by norm_num) (by norm_num)
        (by norm_num [inside_pullX]; exact h.southwestMarker)
        (by norm_num [inside_pullX]; exact own)
        (by norm_num [inside_pullX]; exact h.southwestF0)
        (by norm_num [inside_pullX]; exact fun point =>
          h.apart 4 7 (by decide) _ _ ⟨point,points.1⟩)
        (by norm_num [inside_pullX]; exact fun point =>
          h.apart 4 5 (by decide) _ _ ⟨point,h.southeastSouth⟩)
        (by norm_num [inside_pullX]; exact fun point =>
          h.apart 4 0 (by decide) _ _ ⟨point,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
    have corner := InnerCornerObstruction.corner_excluded_original (q 4) (h.side 4)
      h.southwestMarker h.absentMarker
      (fun own => h.apart 4 0 (by decide) _ _ ⟨own,h.singletonNear⟩)
      (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
      (fun own => h.apart 4 7 (by decide) _ _ ⟨own,points.1⟩)
    exact h.apart 4 7 (by decide) _ _ ⟨(outward_points q h corner missingG3).2.2,points.2⟩

theorem northwest_g4 (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (87/50) 3 := by
  by_contra missingG4
  have f3 := northwest_f3 q h
  have g3 := (g_alternatives q h).resolve_right missingG4
  have f5 : (q 7).Inside 2 (113/50) := by
    by_contra missingF5
    exact C1092MixedSpan.impossible (pullSwap (q 7)) (h.side 7)
      (by norm_num [inside_pullSwap]; exact g3)
      (by norm_num [inside_pullSwap]; exact f3)
      (by norm_num [inside_pullSwap]; exact missingF5)
      (by norm_num [inside_pullSwap]; exact missingG4)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 8 (by decide) _ _ ⟨own,h.leftF1⟩)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 8 (by decide) _ _ ⟨own,h.leftG1⟩)
  have inward := ShortDuplicatePoints.inward_original (pullX (q 7)) (h.side 7)
    (by norm_num [inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullX]; exact f5)
    (by norm_num [inside_pullX]; exact g3)
    (by norm_num [inside_pullX]; exact f3)
    (by norm_num [inside_pullX]; exact missingG4)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
  norm_num [inside_pullX] at inward
  have missingG3 : ¬(q 4).Inside (87/50) 2 :=
    fun own => h.apart 4 7 (by decide) _ _ ⟨own,g3⟩
  have corner := InnerCornerObstruction.inward_corner_excluded_original (q 4) (h.side 4)
    h.southwestMarker h.absentMarker
    (fun own => h.apart 4 0 (by decide) _ _ ⟨own,h.singletonNear⟩)
    (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    (1/2) (26/25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    missingG3 (by
      norm_num
      exact fun own => h.apart 4 7 (by decide) _ _ ⟨own,inward⟩)
  exact h.apart 4 7 (by decide) _ _ ⟨(outward_points q h corner missingG3).2.1,inward⟩

theorem ordinary_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (8/5) 3 ∧ (q 7).Inside (87/50) 3 :=
  ⟨northwest_f3 q h,northwest_g4 q h⟩

#print axioms ordinary_pair
end N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest
