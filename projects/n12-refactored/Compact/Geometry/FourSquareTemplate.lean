import Compact.Geometry.FourSquarePositive
import Compact.Geometry.FourSquareBNegativeCorner
import Compact.Geometry.ClosedFrames

/-! The shared four-square exclusion with no restriction on any square's
orientation. The premises are a subset of the original template's geometric
premises. Canonicalizing faces moves no square and changes no point ownership.
-/

namespace N12Compact.FourSquareTemplate

open S12 S12Pilot FourSquareAnchors

/-- Actual geometric premises, with no angle enclosures or proof-certificate
assumptions. The omitted original points and pairwise inequalities are unused. -/
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
  rRight : ClosedInside R (1543 / 500) 2
  rMissingLow : ¬ R.Inside (81 / 25) (187 / 100)
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)
  br : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)

/-- The entire local four-square theorem, including contact cases and all
orientations. Every branch ends in a proved strict-interior contradiction. -/
theorem impossible (A B L R : OpenSquare) (h : Premises A B L R) : False := by
  obtain ⟨b, bc, bsc, bside, bi, bcl⟩ := ClosedFrames.canonical_frame B
  obtain ⟨l, lc, lsc, lside, li, lcl⟩ := ClosedFrames.canonical_frame L
  have haB : 1 < b.side := by simpa only [bside] using h.one_lt
  have capB : b.side ≤ 1001 / 1000 := by simpa only [bside] using h.side_cap
  have sameA : A.side = b.side := h.sameA.trans bside.symm
  have sameL : b.side = l.side := bside.trans (h.sameL.trans lside.symm)
  have sameR : b.side = R.side := bside.trans h.sameR
  have boxB : InsideContainer b := fun x y hp => h.boxB x y ((bi x y).mp hp)
  have boxL : InsideContainer l := fun x y hp => h.boxL x y ((li x y).mp hp)
  have ab : ∀ x y, ¬ (A.Inside x y ∧ b.Inside x y) :=
    fun x y hp => h.ab x y ⟨hp.1, (bi x y).mp hp.2⟩
  have bl : ∀ x y, ¬ (b.Inside x y ∧ l.Inside x y) :=
    fun x y hp => h.bl x y ⟨(bi x y).mp hp.1, (li x y).mp hp.2⟩
  have br : ∀ x y, ¬ (b.Inside x y ∧ R.Inside x y) :=
    fun x y hp => h.br x y ⟨(bi x y).mp hp.1, hp.2⟩
  have bBottom := (bcl _ _).mpr h.bBottom
  have bTop := (bcl _ _).mpr h.bTop
  have bTopRight := (bcl _ _).mpr h.bTopRight
  have bMissingLeft : ¬ b.Inside 1 (1543 / 500) :=
    fun hp => h.bMissingLeft ((bi _ _).mp hp)
  have bMissingRight : ¬ b.Inside 2 (1543 / 500) :=
    fun hp => h.bMissingRight ((bi _ _).mp hp)
  have lLeft := (lcl _ _).mpr h.lLeft
  have lTop := (lcl _ _).mpr h.lTop
  have lMissingLow : ¬ l.Inside (19 / 25) (187 / 100) :=
    fun hp => h.lMissingLow ((li _ _).mp hp)
  have lMissingRight : ¬ l.Inside (33 / 20) (33 / 20) :=
    fun hp => h.lMissingRight ((li _ _).mp hp)
  by_cases bs : 0 ≤ b.s
  · exact FourSquarePositive.impossible A b l R haB capB sameA sameL sameR
      bc bs (abs_le.mp bsc).2 lc lsc boxB boxL h.boxR
      h.aP h.aQ h.aT h.aF h.aG bBottom bTop bTopRight bMissingLeft bMissingRight
      lLeft lTop lMissingLow lMissingRight h.rTop h.rRight h.rMissingLow ab h.ar bl br
  · have haA : 1 < A.side := by simpa only [sameA] using haB
    have haR : 1 < R.side := by simpa only [sameR] using haB
    have haL : 1 < l.side := by simpa only [sameL] using haB
    have highA := FourSquareAAll.point A b R haA haR h.boxR h.aP h.aQ h.aT
      h.aF h.aG bBottom h.rTop h.rRight h.rMissingLow ab h.ar
    have rowA := FourSquareAForced.row_point A h.aP highA
    have ba : ∀ x y, ¬ (b.Inside x y ∧ A.Inside x y) :=
      fun x y hp => ab x y ⟨hp.2, hp.1⟩
    have short := FourSquareBCorner.no_long_section A b l R boxB lTop rowA h.rTop bl ba br
    have rowMissing := ClosedPointExclusion.outside_of_closed b l _ _ bl lTop
    have targetMissing : ¬ b.Inside 2 (5 / 2) := fun hp => ab _ _ ⟨highA, hp⟩
    exact FourSquareBNegativeCorner.exclude b l bc (le_of_not_ge bs)
      (by linarith only [(abs_le.mp bsc).1]) lc lsc haB capB haL boxL
      bBottom bTop bTopRight lLeft lTop bMissingLeft bMissingRight
      rowMissing targetMissing lMissingLow lMissingRight bl short

#print axioms impossible
end N12Compact.FourSquareTemplate
