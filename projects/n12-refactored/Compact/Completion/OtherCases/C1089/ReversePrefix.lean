import Compact.Completion.OtherCases.C1089.WallCore
import Compact.Completion.OtherCases.C1090.NESelectionOwners
import Compact.Completion.OtherCases.C1089.WallOrigins
import Compact.Geometry.WallUpperMissingReach
import Compact.Geometry.WallLowerReach
import Compact.Completion.C981.Crosspoint
import Compact.Completion.OtherCases.ElbowPoint

/-! The reverse-cycle entrance on the actual unmerged C1089 owners.
The ordinary left bar is derived from its genuine F0/G0 pair, not from
the nonexistent merged marker1. NW's original marker remains in Q7.
The true singleton supplies the separate horizontal bar. Source only.
-/
namespace N12Compact.Completion.OtherCases.C1089.Reverse
open S12 S12Pilot OriginalData WallCore
set_option Elab.async false
noncomputable section

/-- Exactly the actual points used by the common structural arguments.
This interface has no merged marker or strengthened left-bar premise. -/
structure PointTable (q : Fin 12 → OpenSquare) : Prop extends Frame q where
  southwestF4 : (q 4).Inside 2 (87/50)
  southwestG3 : (q 4).Inside (87/50) 2
  southwestSouth : (q 4).Inside 2 (3/2)
  southwestWest : (q 4).Inside (3/2) 2
  southeastF8 : (q 5).Inside 3 (87/50)
  southeastG8 : (q 5).Inside 3 (8/5)
  northeastFCover : (q 6).Inside 2 (113/50) ∨
    (q 6).Inside (12/5) 3 ∨ (q 6).Inside 3 (113/50)
  northeastG7 : (q 6).Inside (113/50) 3
  northwestF1 : (q 7).Inside 1 (113/50)
  northwestG1 : (q 7).Inside 1 (12/5)
  leftF0 : (q 8).Inside 1 (87/50)
  leftG0 : (q 8).Inside 1 (8/5)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  bottomAdvance : (q 9).Inside (14/5) 1
  bottomBar : ∀ x : ℝ,113/50≤x → x≤14/5 → (q 9).Inside x 1
  rightF9 : (q 10).Inside 3 (113/50)
  rightG9 : (q 10).Inside 3 (12/5)
  rightAdvance : (q 10).Inside 3 (64/25)
  rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → (q 10).Inside 3 y
  topF3 : (q 11).Inside (8/5) 3
  topG4 : (q 11).Inside (87/50) 3
  topOrigin : (q 11).Inside 2 3

theorem point_table (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : centerY (owners p 8)≤2) (top : centerX (owners p 11)≤2) :
    PointTable (owners p) := by
  let h := frame p hf
  have a := southwest_inward p hf left
  have topG4 := top_low p hf top (87/50) (by norm_num) (by norm_num)
  have ng1 : (owners p 7).Inside 1 (12/5) := by
    rcases AuxiliaryCover.northwest_g_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 7 4 (by decide) _ _ ⟨own,a.2⟩)
    · exact False.elim (h.apart 7 11 (by decide) _ _ ⟨own,topG4⟩)
  have nf1 : (owners p 7).Inside 1 (113/50) := by
    by_contra missing
    have f3 : (owners p 7).Inside (8/5) 3 := by
      by_contra noF3
      have f5 : (owners p 7).Inside 2 (113/50) := by
        rcases AuxiliaryCover.northwest_f_cover p hf with own | own | own
        · exact False.elim (missing own)
        · exact False.elim (noF3 own)
        · exact own
      exact C1092MixedSpan.impossible (pullY (pullX (owners p 7))) (h.side 7)
        (by norm_num [inside_pullY,inside_pullX]; exact f5)
        (by norm_num [inside_pullY,inside_pullX]; exact ng1)
        (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
          h.apart 7 4 (by decide) _ _ ⟨own,a.2⟩)
        (by norm_num [inside_pullY,inside_pullX]; exact missing)
        (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
          h.apart 7 11 (by decide) _ _ ⟨own,topG4⟩)
        (by norm_num [inside_pullY,inside_pullX]; exact noF3)
    exact C1092CornerTwoGaps.impossible (pullX (owners p 7)) (h.side 7)
      (39/100) (13/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [inside_pullX]; exact h.northwestMarker)
      (by norm_num [inside_pullX]; exact f3)
      (by norm_num [inside_pullX]; exact ng1)
      (by norm_num [inside_pullX]; exact fun own => h.apart 7 11 (by decide) _ _
        ⟨own,top_low p hf top _ (by norm_num) (by norm_num)⟩)
      (by norm_num [inside_pullX]; exact missing)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 7 3 (by decide) _ _ ⟨own,h.northwestCorner⟩)
  have lf0 := left_low p hf left (87/50) (by norm_num) (by norm_num)
  have lg0 : (owners p 8).Inside 1 (8/5) := by
    rcases AuxiliaryCover.left_g_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 8 7 (by decide) _ _ ⟨own,ng1⟩)
    · exact False.elim (h.apart 8 4 (by decide) _ _ ⟨own,a.2⟩)
  have lowLeft : (owners p 8).Inside 1 (36/25) := by
    have point := WallLowerReach.point (pullY (owners p 8)) (h.side 8)
      (container_pullY _ (h.box 8))
      (by norm_num [inside_pullY]; exact h.leftMarker)
      (by norm_num [inside_pullY]; exact lg0)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 8 7 (by decide) _ _ ⟨own,nf1⟩)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 8 4 (by decide) _ _ ⟨own,a.2⟩)
    norm_num [inside_pullY] at point
    exact point
  have leftBar (y : ℝ) (low : 36/25≤y) (high : y≤87/50) :
      (owners p 8).Inside 1 y :=
    CommonCases.OriginalOwners.vertical_segment _ _ _ _ _ lowLeft lf0 (by norm_num) low high
  have aSouth : (owners p 4).Inside 2 (3/2) := by
    have point := C981CompletionCrosspoint.point (pullY (pullX (owners p 4))) (h.side 4)
      (by norm_num [inside_pullY,inside_pullX]; exact a.1)
      (by norm_num [inside_pullY,inside_pullX]; exact a.2)
      (by norm_num [inside_pullY,inside_pullX]; exact h.southwestMarker)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 4 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own => h.apart 4 8 (by decide) _ _
        ⟨own,leftBar _ (by norm_num) (by norm_num)⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own => h.apart 4 8 (by decide) _ _
        ⟨own,leftBar _ (by norm_num) (by norm_num)⟩)
    norm_num [inside_pullY,inside_pullX] at point
    exact point
  have aWest : (owners p 4).Inside (3/2) 2 := by
    have point := C981CompletionCrosspoint.point (pullSwap (pullY (pullX (owners p 4))))
      (h.side 4)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact a.2)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact a.1)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestMarker)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
        h.apart 4 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
        h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own => h.apart 4 0
        (by decide) _ _ ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
      (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own => h.apart 4 0
        (by decide) _ _ ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
    norm_num [inside_pullSwap,inside_pullY,inside_pullX] at point
    exact point
  have sf8 : (owners p 5).Inside 3 (87/50) := by
    rcases AuxiliaryCover.southeast_f_cover p hf with own | own | own
    · exact False.elim (h.apart 5 4 (by decide) _ _ ⟨own,a.1⟩)
    · exact False.elim (h.apart 5 9 (by decide) _ _ ⟨own,DirectDomains.bottom_far p hf⟩)
    · exact own
  have sg8 : (owners p 5).Inside 3 (8/5) := by
    by_contra missing
    have g6 : (owners p 5).Inside (113/50) 2 := by
      rcases AuxiliaryCover.southeast_g_cover p hf with own | own | own
      · exact False.elim (h.apart 5 9 (by decide) _ _
          ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
      · exact own
      · exact False.elim (missing own)
    have point := (ElbowPoint.points_original _ (h.side 5) h.southeastMarker g6 sf8
      (fun own => h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩) missing
      (fun own => h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩)).1
    exact h.apart 4 5 (by decide) _ _ ⟨aSouth,point⟩
  have r := DirectDomains.right_high_pair p hf
    (fun own => h.apart 10 5 (by decide) _ _ ⟨own,sf8⟩)
  have selectionData : C1090.NESelectionOwners.Data (owners p) := {
    side := h.side
    apart := h.apart
    southeastMarker := h.southeastMarker
    southeastF8 := sf8
    southeastG8 := sg8
    northeastMarker := h.northeastMarker
    northwestMarker := h.northwestMarker
    cornerPoint := h.southeastCorner
    cornerMarker := h.southeastCornerRight
    rightMarker := h.rightMarker
    rightF9 := r.1
    rightG9 := r.2
    bottomG5 := (bottom p hf).2.2 _ (by norm_num) (by norm_num)
    bottomAdvance := (bottom p hf).2.1
    fCover := by
      rcases AuxiliaryCover.northeast_f_cover p hf with own | own | own
      · exact Or.inl own
      · exact Or.inr own
      · exact False.elim (h.apart 6 10 (by decide) _ _ ⟨own,r.1⟩)
    gCover := by
      rcases AuxiliaryCover.northeast_g_cover p hf with own | own | own
      · exact Or.inl own
      · exact Or.inr own
      · exact False.elim (h.apart 6 10 (by decide) _ _ ⟨own,r.2⟩) }
  have eg7 := (C1090.NESelectionOwners.selection (owners p) selectionData).1
  have tf3 : (owners p 11).Inside (8/5) 3 := by
    rcases DirectDomains.top_component p hf with own | pair
    · exact False.elim (h.apart 11 6 (by decide) _ _ ⟨own,eg7⟩)
    · exact pair.1
  have rAdvance : (owners p 10).Inside 3 (64/25) := by
    have point := WallUpperMissingReach.point (pullX (owners p 10)) (h.side 10)
      (container_pullX _ (h.box 10))
      (by norm_num [inside_pullX]; exact h.rightMarker)
      (by norm_num [inside_pullX]; exact r.2)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 10 5 (by decide) _ _ ⟨own,sf8⟩)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 10 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    norm_num [inside_pullX] at point
    exact point
  exact {
    toFrame := h
    southwestF4 := a.1
    southwestG3 := a.2
    southwestSouth := aSouth
    southwestWest := aWest
    southeastF8 := sf8
    southeastG8 := sg8
    northeastFCover := AuxiliaryCover.northeast_f_cover p hf
    northeastG7 := eg7
    northwestF1 := nf1
    northwestG1 := ng1
    leftF0 := lf0
    leftG0 := lg0
    bottomF6 := DirectDomains.bottom_far p hf
    bottomG5 := (bottom p hf).2.2 _ (by norm_num) (by norm_num)
    bottomAdvance := (bottom p hf).2.1
    bottomBar := (bottom p hf).2.2
    rightF9 := r.1
    rightG9 := r.2
    rightAdvance := rAdvance
    rightBar := fun y low high => CommonCases.OriginalOwners.vertical_segment _ _ _ _ _
      r.1 rAdvance (by norm_num) low high
    topF3 := tf3
    topG4 := topG4
    topOrigin := WallOrigins.top_origin_from_northwest (owners p) h.side h.same h.box h.apart
      h.northwestMarker nf1 ng1 a.2 h.leftMarker topG4 h.topMarker
      h.northwestCornerTop h.northwestCorner }

end
#print axioms point_table
end N12Compact.Completion.OtherCases.C1089.Reverse
