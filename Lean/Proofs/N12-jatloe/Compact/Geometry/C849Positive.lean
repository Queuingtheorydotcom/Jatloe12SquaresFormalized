import Compact.Geometry.C849ShallowAB

/-! Complete positive canonical-B sector for the actual 849/851 geometry.
The squares A, B, R, C and E remain original OpenSquares. In particular the
foreign points below are consequences of actual disjointness, not substitutes
for the A/R geometric constraints. The negative B sector is separate. -/
namespace N12Compact.C849Positive

open S12 S12Pilot FourSquareAnchors

/-- A strictly owned point of the real C square caps B's U face. -/
theorem right_cap (B C : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (high : B.Inside 2 (1543/500))
    (cq : C.Inside (113/50) 3)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ C.Inside x y)) :
    B.loU+B.side ≤ (113/50)*B.c+3*B.s := by
  have lowerU : B.loU < B.c*(113/50)+B.s*3 := by
    linarith only [top.1,bc]
  have lowerV : B.loV < -B.s*(113/50)+B.c*3 := by
    linarith only [bottom.2.2.1,bsc,bc]
  have upperV : -B.s*(113/50)+B.c*3 < B.loV+B.side := by
    linarith only [high.2.2.2,bc,bs]
  apply le_of_not_gt
  intro upperU
  exact apart _ _ ⟨⟨lowerU,by linarith only [upperU],lowerV,upperV⟩,cq⟩

/-- Every angle of a positive canonical B frame is excluded. No extra
orientation assumption is made about any of the other four squares. -/
theorem impossible (A B R C E : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (same : A.side = B.side) (ha : 1 < B.side) (hr : 1 < R.side)
    (boxR : InsideContainer R)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20))
    (missingF : ¬ A.Inside (33/20) (33/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (bT : ClosedInside B (33/20) (47/20))
    (bP : ClosedInside B (8/5) 3) (bH : B.Inside 2 (1543/500))
    (r₀ : ClosedInside R 3 (12/5)) (r₁ : ClosedInside R (1543/500) 2)
    (rW : ¬ R.Inside (81/25) (187/100))
    (cQ : C.Inside (113/50) 3) (eP : E.Inside 1 3)
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (bcApart : ∀ x y, ¬ (B.Inside x y ∧ C.Inside x y))
    (be : ∀ x y, ¬ (B.Inside x y ∧ E.Inside x y)) : False := by
  have aTclosed : ClosedInside A (47/20) (47/20) :=
    ⟨aT.1.le,aT.2.1.le,aT.2.2.1.le,aT.2.2.2.le⟩
  have aHigh := FourSquareAAll.point A B R (by simpa only [same] using ha) hr boxR
    aP aQ aTclosed missingF missingG bT r₀ r₁ rW ab ar
  have lower := C849PositiveAbove.b_lower_face B bc bs bT bH
    (fun h => ab _ _ ⟨aHigh,h⟩)
  have lowSlope : 3*B.c ≤ 7*B.s := by linarith only [lower,bT.2.2.1]
  have missingE : ¬ B.Inside 1 3 := fun h => be _ _ ⟨h,eP⟩
  rcases PositiveBLeftReduction.upper_left_marker_modes B bc bs ha bT bP lower missingE with
    lowerU | ⟨upperV,height,_⟩
  · have cap := right_cap B C bc bs bsc bT bP bH cQ bcApart
    have cLow : 50/63 < B.c := by linarith only [lowerU,cap,ha]
    have highSlope : B.s ≤ (4/5)*B.c := by
      by_contra failure
      have first := mul_pos (sub_pos.mpr (lt_of_not_ge failure))
        (show 0 < B.s+(4/5)*B.c by linarith only [bs,bc])
      have second := mul_pos (sub_pos.mpr cLow)
        (show 0 < B.c+50/63 by linarith only [bc])
      nlinarith only [first,second,B.unit_normal]
    have outsideB := ClosedPointExclusion.outside_of_closed A B _ _ ab bT
    have outsideR := ClosedPointExclusion.outside_of_closed A R _ _ ar r₀
    obtain ⟨A',ap,aq,side,inside,closed⟩ := ClosedFrames.positive_frame A
    exact C849ShallowAB.in_frame A' B ap aq bc bs lowSlope highSlope
      (side.trans same) ha ((closed _ _).mpr aP) ((closed _ _).mpr aQ)
      ((inside _ _).mpr aT) (fun h => missingG ((inside _ _).mp h))
      (fun h => outsideB ((inside _ _).mp h))
      (fun h => outsideR ((inside _ _).mp h)) bT bH
      (fun x y h => ab x y ⟨(inside x y).mp h.1,h.2⟩)
  · exact C849SteepAB.impossible A B R bc bs bsc same ha hr boxR
      aP aQ aT missingF missingG bT bH r₀ r₁ rW ab ar upperV

#print axioms impossible

end N12Compact.C849Positive
