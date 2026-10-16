import Compact.Geometry.FourSquareTemplate

/-! The shared geometric endgame stated at the higher right-point boundary.
It can use either wall barrier theorem. No enclosure, angle grid, or assumed
case exclusion is part of this interface. -/
namespace N12Compact.FourSquareHighRight

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare
open C977ChainBridge FourSquareBCorner FourSquareBLBridge

/-- Original template geometry, with the right barrier supplied separately
through the actual higher point of R. -/
structure Premises (A B L R : OpenSquare) : Prop where
  one_lt : 1 < B.side
  side_cap : B.side ≤ 1001 / 1000
  sameA : A.side = B.side
  sameL : B.side = L.side
  sameR : B.side = R.side
  boxB : InsideContainer B
  boxL : InsideContainer L
  boxR : InsideContainer R
  aP : ClosedInside A 2 (113 / 50)
  aQ : ClosedInside A (113 / 50) 2
  aT : ClosedInside A (47 / 20) (47 / 20)
  aF : ¬ A.Inside (33 / 20) (33 / 20)
  aG : ¬ A.Inside (47 / 20) (33 / 20)
  bBottom : ClosedInside B (33 / 20) (47 / 20)
  bTop : ClosedInside B (8 / 5) 3
  bTopRight : ClosedInside B (87 / 50) 3
  bMissingLeft : ¬ B.Inside 1 (1543 / 500)
  bMissingRight : ¬ B.Inside 2 (1543 / 500)
  lLeft : ClosedInside L (457 / 500) 2
  lTop : ClosedInside L 1 (12 / 5)
  lMissingLow : ¬ L.Inside (19 / 25) (187 / 100)
  lMissingRight : ¬ L.Inside (33 / 20) (33 / 20)
  rTop : ClosedInside R 3 (12 / 5)
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)
  br : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)

theorem impossible (A B L R : OpenSquare) (h : Premises A B L R)
    (rHigh : R.Inside 3 (5/2)) : False := by
  have haA : 1 < A.side := by simpa only [h.sameA] using h.one_lt
  have bOutside := ClosedPointExclusion.outside_of_closed A B _ _ h.ab h.bBottom
  have rOutside := ClosedPointExclusion.outside_of_closed A R _ _ h.ar h.rTop
  have rHighOutside : ¬ A.Inside 3 (5/2) := fun hp => h.ar _ _ ⟨hp, rHigh⟩
  obtain ⟨q, qc, qs, qside, qi, qcl⟩ := ClosedFrames.positive_frame A
  have qPoint := FourSquareANarrow.point_of_higher_R q
    (by simpa only [qside] using haA) qc qs
    ((qcl _ _).mpr h.aP) ((qcl _ _).mpr h.aQ) ((qcl _ _).mpr h.aT)
    (fun hp => h.aF ((qi _ _).mp hp)) (fun hp => h.aG ((qi _ _).mp hp))
    (fun hp => bOutside ((qi _ _).mp hp)) (fun hp => rOutside ((qi _ _).mp hp))
    (fun hp => rHighOutside ((qi _ _).mp hp))
  have highA : A.Inside 2 (5/2) := (qi _ _).mp qPoint
  have rowA := FourSquareAForced.row_point A h.aP highA
  obtain ⟨b, bc, bsc, bside, bi, bcl⟩ := ClosedFrames.canonical_frame B
  obtain ⟨l, lc, lsc, lside, li, lcl⟩ := ClosedFrames.canonical_frame L
  have haB : 1 < b.side := by simpa only [bside] using h.one_lt
  have capB : b.side ≤ 1001/1000 := by simpa only [bside] using h.side_cap
  have sameL : b.side = l.side := bside.trans (h.sameL.trans lside.symm)
  have haL : 1 < l.side := by simpa only [sameL] using haB
  have boxB : InsideContainer b := fun x y hp => h.boxB x y ((bi x y).mp hp)
  have boxL : InsideContainer l := fun x y hp => h.boxL x y ((li x y).mp hp)
  have ab : ∀ x y, ¬ (A.Inside x y ∧ b.Inside x y) :=
    fun x y hp => h.ab x y ⟨hp.1, (bi x y).mp hp.2⟩
  have bl : ∀ x y, ¬ (b.Inside x y ∧ l.Inside x y) :=
    fun x y hp => h.bl x y ⟨(bi x y).mp hp.1, (li x y).mp hp.2⟩
  have br : ∀ x y, ¬ (b.Inside x y ∧ R.Inside x y) :=
    fun x y hp => h.br x y ⟨(bi x y).mp hp.1, hp.2⟩
  have ba : ∀ x y, ¬ (b.Inside x y ∧ A.Inside x y) :=
    fun x y hp => ab x y ⟨hp.2, hp.1⟩
  have bottom := (bcl _ _).mpr h.bBottom
  have top := (bcl _ _).mpr h.bTop
  have topRight := (bcl _ _).mpr h.bTopRight
  have missingLeft : ¬ b.Inside 1 (1543/500) :=
    fun hp => h.bMissingLeft ((bi _ _).mp hp)
  have missingRight : ¬ b.Inside 2 (1543/500) :=
    fun hp => h.bMissingRight ((bi _ _).mp hp)
  have lLeft := (lcl _ _).mpr h.lLeft
  have lTop := (lcl _ _).mpr h.lTop
  have lMissingLow : ¬ l.Inside (19/25) (187/100) :=
    fun hp => h.lMissingLow ((li _ _).mp hp)
  have lMissingRight : ¬ l.Inside (33/20) (33/20) :=
    fun hp => h.lMissingRight ((li _ _).mp hp)
  have short := no_long_section A b l R boxB lTop rowA h.rTop bl ba br
  have rowMissing := ClosedPointExclusion.outside_of_closed b l _ _ bl lTop
  have targetMissing : ¬ b.Inside 2 (5/2) := fun hp => ab _ _ ⟨highA, hp⟩
  by_cases bs : 0 ≤ b.s
  · have bsc' : b.s ≤ b.c := (abs_le.mp bsc).2
    have high := center_above_radius b bc.le bs bsc' haB capB top short
    obtain ⟨cornerU, cornerV⟩ := upper_corner b bc bs bsc' haB capB
      bottom top topRight missingLeft missingRight short
    have steep := (corner_steep b bc.le bs bsc' haB high cornerU cornerV).2
    obtain ⟨bottomV, height, wide⟩ := forced_lower_V b bc bs bsc' haB steep
      bottom top topRight rowMissing targetMissing cornerV
    have axes := BLLongitudinal.two_directed_alternatives b l bc bs bsc' lc lsc
      haL bottom top lLeft lTop lMissingLow lMissingRight sameL bl
    have lowV := missing_below_V b l bc bs bsc' lc lsc haB haL
      bottom top lLeft lTop lMissingLow lMissingRight cornerU cornerV bl
    have dot := dot_nonneg b l bc.le bs bsc' lc.le lsc
    rcases axes with baxis | laxis
    · have cap := right_axis_cap b l baxis
      have radius : supportRadius l b.c b.s = b.side/2 *
          ((b.c*l.c+b.s*l.s)+|b.c*l.s-b.s*l.c|) := by
        have cross : -b.c*l.s+b.s*l.c = -(b.c*l.s-b.s*l.c) := by ring
        simp only [supportRadius, cross, abs_neg, abs_of_nonneg dot, sameL]
      rw [radius] at cap
      have axis : b.c*centerX l+b.s*centerY l+b.side/2 *
          ((b.c*l.c+b.s*l.s)+|b.c*l.s-b.s*l.c|)+b.side ≤
          2*b.c+(1543/500)*b.s := by linarith only [cap, cornerU]
      have wall : b.side*(l.c+|l.s|)/2 ≤ centerX l := by
        simpa only [sameL] using left_wall l lc.le boxL
      have vcenter : -l.s*(19/25)+l.c*(187/100) ≤
          -l.s*centerX l+l.c*centerY l-b.side/2 := by
        have hh := (center_coordinates l).2
        rw [← sameL] at hh
        linarith only [lowV, hh]
      exact FourSquareLongitudinal.b_axis_impossible
        b.side b.c b.s l.c l.s (centerX l) (centerY l)
        haB bc bs bsc' lc lsc b.unit_normal l.unit_normal wall vcenter height axis
    · have walls := left_upper_bounds l lc boxL lLeft lowV
      have caps := right_minimum_bounds b l dot cornerU cornerV bottomV laxis
      exact FourSquareLongitudinal.l_axis_impossible
        b.side b.c b.s l.c l.s (l.loU+l.side)
        haB bc bs bsc' lc lsc b.unit_normal l.unit_normal wide
        (by simpa only [sameL] using walls.1)
        (by simpa only [sameL] using walls.2)
        (by intro ht; have hh := caps.1 ht; nlinarith only [hh]) caps.2
  · exact FourSquareBNegativeCorner.exclude b l bc (le_of_not_ge bs)
      (by linarith only [(abs_le.mp bsc).1]) lc lsc haB capB haL boxL
      bottom top topRight lLeft lTop missingLeft missingRight
      rowMissing targetMissing lMissingLow lMissingRight bl short

#print axioms impossible
end N12Compact.FourSquareHighRight
