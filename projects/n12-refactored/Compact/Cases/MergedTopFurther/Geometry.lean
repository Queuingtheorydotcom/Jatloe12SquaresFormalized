import Compact.Geometry.C849Positive
import Compact.Geometry.C849Negative
import S12.Convex

/-! Reuse of the complete merged-top argument when the foreign right-hand
row is supplied by an actual singleton square's interior vertical segment,
rather than by the separate right-wall square. -/
namespace N12Compact.MergedTopFurther.Geometry
open S12 S12Pilot FourSquareAnchors

theorem right_points (R : OpenSquare)
    (low : R.Inside 3 (113/50)) (high : R.Inside 3 (72/25)) :
    R.Inside 3 (12/5) ∧ R.Inside 3 (5/2) := by
  constructor
  · convert inside_segment R 3 (113/50) 3 (72/25) (7/31) low high
      (by norm_num) (by norm_num) using 1 <;> norm_num
  · convert inside_segment R 3 (113/50) 3 (72/25) (12/31) low high
      (by norm_num) (by norm_num) using 1 <;> norm_num

theorem a_high (A B R : OpenSquare) (ha : 1 < A.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : ClosedInside A (47/20) (47/20))
    (missingF : ¬ A.Inside (33/20) (33/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (bT : ClosedInside B (33/20) (47/20))
    (rLow : R.Inside 3 (113/50)) (rHigh : R.Inside 3 (72/25))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) :
    A.Inside 2 (5/2) := by
  have points := right_points R rLow rHigh
  have outsideB := ClosedPointExclusion.outside_of_closed A B _ _ ab bT
  obtain ⟨q,hc,hs,side,inside,closed⟩ := ClosedFrames.positive_frame A
  have point := FourSquareANarrow.point_of_higher_R q (by simpa only [side] using ha)
    hc hs ((closed _ _).mpr aP) ((closed _ _).mpr aQ) ((closed _ _).mpr aT)
    (fun h => missingF ((inside _ _).mp h))
    (fun h => missingG ((inside _ _).mp h))
    (fun h => outsideB ((inside _ _).mp h))
    (fun h => ar _ _ ⟨(inside _ _).mp h,points.1⟩)
    (fun h => ar _ _ ⟨(inside _ _).mp h,points.2⟩)
  exact (inside _ _).mp point

/-- The existing positive-B scalar endgame depends only on the genuine
foreign row point and the already derived A point. -/
theorem positive_impossible (A B C E : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (same : A.side=B.side) (ha : 1 < B.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20)) (aHigh : A.Inside 2 (5/2))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingR : ¬ A.Inside 3 (12/5))
    (bT : ClosedInside B (33/20) (47/20)) (bP : ClosedInside B (8/5) 3)
    (bH : B.Inside 2 (1543/500))
    (cQ : C.Inside (113/50) 3) (eP : E.Inside 1 3)
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (bcApart : ∀ x y, ¬ (B.Inside x y ∧ C.Inside x y))
    (be : ∀ x y, ¬ (B.Inside x y ∧ E.Inside x y)) : False := by
  have lower := C849PositiveAbove.b_lower_face B bc bs bT bH
    (fun h => ab _ _ ⟨aHigh,h⟩)
  have lowSlope : 3*B.c ≤ 7*B.s := by linarith only [lower,bT.2.2.1]
  have missingE : ¬ B.Inside 1 3 := fun h => be _ _ ⟨h,eP⟩
  have outsideB := ClosedPointExclusion.outside_of_closed A B _ _ ab bT
  obtain ⟨A',ap,aq,side,inside,closed⟩ := ClosedFrames.positive_frame A
  rcases PositiveBLeftReduction.upper_left_marker_modes B bc bs ha bT bP lower missingE with
    lowerU | ⟨upperV,height,_⟩
  · have cap := C849Positive.right_cap B C bc bs bsc bT bP bH cQ bcApart
    have cLow : 50/63 < B.c := by linarith only [lowerU,cap,ha]
    have highSlope : B.s ≤ (4/5)*B.c := by
      apply le_of_not_gt
      intro failure
      have first := mul_pos (sub_pos.mpr failure)
        (show 0 < B.s+(4/5)*B.c by linarith only [bs,bc])
      have second := mul_pos (sub_pos.mpr cLow)
        (show 0 < B.c+50/63 by linarith only [bc])
      nlinarith only [first,second,B.unit_normal]
    exact C849ShallowAB.in_frame A' B ap aq bc bs lowSlope highSlope
      (side.trans same) ha ((closed _ _).mpr aP) ((closed _ _).mpr aQ)
      ((inside _ _).mpr aT) (fun h => missingG ((inside _ _).mp h))
      (fun h => outsideB ((inside _ _).mp h)) (fun h => missingR ((inside _ _).mp h))
      bT bH (fun x y h => ab x y ⟨(inside x y).mp h.1,h.2⟩)
  · exact C849SteepAB.in_frame A' B ap aq bc bs bsc (side.trans same) ha height upperV
      ((closed _ _).mpr aP) ((closed _ _).mpr aQ) ((inside _ _).mpr aT)
      (fun h => missingG ((inside _ _).mp h)) (fun h => outsideB ((inside _ _).mp h))
      (fun h => missingR ((inside _ _).mp h)) bT bH
      (fun x y h => ab x y ⟨(inside x y).mp h.1,h.2⟩)

#print axioms positive_impossible
end N12Compact.MergedTopFurther.Geometry
