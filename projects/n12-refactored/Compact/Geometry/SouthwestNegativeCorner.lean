import Compact.Geometry.C696PositiveCorner
import Compact.Geometry.ClosedFrames

/-! The full negative-central sector with no restriction on the actual
bottom singleton's orientation. Canonicalizing a square changes its frame
description only; all points, containment and disjointness are transported
through the proved inside equivalence. The remaining positive-central
sector is not asserted by this module. -/
namespace N12Compact.SouthwestNegativeCorner

open S12 S12Pilot FourSquareAnchors C977CornerCubic

theorem point (O A L : OpenSquare) (T : ℝ) (hs : A.s=-T)
    (normalA : Normal A.c T) (same : O.side=A.side)
    (side : 1<A.side) (box : InsideContainer O)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25))
    (missing : ¬O.Inside 1 1) (missingM : ¬O.Inside 2 (457/500))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aE : A.Inside (87/50) 2) (aNew : A.Inside (3/2) 2)
    (lN : L.Inside 1 (28/25)) (lW : L.Inside 1 (87/50))
    (oa : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (al : ∀ x y, ¬(A.Inside x y ∧ L.Inside x y)) : A.Inside 2 2 := by
  obtain ⟨r,hc,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame O
  have rsame : r.side=A.side := shape.trans same
  have rside : 1<r.side := by simpa only [rsame] using side
  have rbox : InsideContainer r := fun x y h => box x y ((inside x y).mp h)
  have rM := (inside 1 (457/500)).mpr oM
  have rN := (inside (28/25) 1).mpr oN
  have rF := (inside (187/100) (19/25)).mpr oF
  have rmissing : ¬r.Inside 1 1 := fun h => missing ((inside 1 1).mp h)
  have rmissingM : ¬r.Inside 2 (457/500) :=
    fun h => missingM ((inside 2 (457/500)).mp h)
  have ra : ∀ x y, ¬(r.Inside x y ∧ A.Inside x y) := by
    intro x y h
    exact oa x y ⟨(inside x y).mp h.1,h.2⟩
  by_cases nonnegative : 0≤r.s
  · have normalR : Normal r.c r.s :=
      ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using canonical,r.unit_normal⟩
    exact C696PositiveCorner.point r A L T hs normalR normalA rsame side rbox
      rM rN rF rmissing rmissingM aP aD aE aNew lN lW ra al
  · have negative : r.s≤0 := le_of_lt (lt_of_not_ge nonnegative)
    have normalR : Normal r.c (-r.s) := ⟨by linarith only [negative],
      by simpa only [abs_of_nonpos negative] using canonical,
      by nlinarith only [r.unit_normal]⟩
    exact C977NegativeCorner.point r A L (-r.s) T (by ring) hs normalR normalA
      rside rsame rbox rM rN rF rmissing aP aD aE lN lW ra al

end N12Compact.SouthwestNegativeCorner
