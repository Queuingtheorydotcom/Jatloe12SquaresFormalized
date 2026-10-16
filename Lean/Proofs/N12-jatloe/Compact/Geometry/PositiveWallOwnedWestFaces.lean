import Compact.Geometry.PositiveWallMarker

/-! Genuine positive-wall faces when the central square owns (1,2).
The paired upper corner's separately proved outward point (.8,3) is
explicit. Both possible upper-marker escapes are retained and resolved
using the actual left wall and the foreign lower-singleton far point.
No point at height 2.88 occurs. Source only, uncompiled. -/
namespace N12Compact.PositiveWallOwnedWestFaces

open S12 S12Pilot FourSquareAnchors ThreeSquare
open C977CornerCubic

theorem lower_face (W : OpenSquare) (wn : Normal W.c W.s)
    (marker : W.Inside (457/500) 2) (high : W.Inside 1 (12/5))
    (missing : ¬W.Inside 1 2) : 2*W.c-W.s≤W.loV := by
  have wb := normal_bounds wn
  have wc : 0<W.c := by linarith only [wb.1]
  apply le_of_not_gt
  intro lower
  apply missing
  refine ⟨?_, ?_, (by linarith only [lower]), ?_⟩ <;>
    linarith only [marker.1,high.2.1,high.2.2.2,wc,wn.1]

private theorem sum_margin {d t : ℝ} (wn : Normal d t) :
    1+(4/5)*d*t≤d+t := by
  have b := normal_bounds wn
  have product := mul_nonneg
    (show 0≤d+t-1 by linarith only [b.2.2.2.2.1])
    (show 0≤3/2-(d+t) by linarith only [b.2.2.2.2.2])
  nlinarith only [product,wn.2.2]

/-- The actual upper marker escapes only above V once the genuine
outward corner point is foreign. The full square wall constraint is
essential in eliminating the U escape. -/
theorem upper_v (W : OpenSquare) (wn : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (high : W.Inside 1 (12/5))
    (missingWest : ¬W.Inside 1 2)
    (missingFar : ¬W.Inside (19/25) (187/100))
    (missingTop : ¬W.Inside (457/500) 3)
    (missingOut : ¬W.Inside (4/5) 3) :
    W.loV+W.side≤3*W.c-(457/500)*W.s := by
  have wb := normal_bounds wn
  have wc : 0<W.c := by linarith only [wb.1]
  have lower := lower_face W wn marker high missingWest
  rcases PositiveWallMarker.upper_faces W wn marker missingTop with capU | capV
  · have wall0 := FourSquareBLBridge.left_wall W wc.le box
    rw [abs_of_nonneg wn.1] at wall0
    dsimp [centerX] at wall0
    have wall : W.s*(W.loV+W.side)≤W.c*W.loU := by
      nlinarith only [wall0]
    have width := mul_pos (sub_pos.mpr side)
      (show 0<W.c+W.s by linarith only [wc,wn.1])
    have lowWeighted := mul_nonneg wn.1 (sub_nonneg.mpr lower)
    have upperWeighted := mul_nonneg wc.le (sub_nonneg.mpr capU)
    have necessary : (43/500)*W.c^2<(1-W.c)*(1-W.s) := by
      nlinarith only [wall,width,lowWeighted,upperWeighted,wn.2.2]
    have deficit := mul_nonneg wc.le (sub_nonneg.mpr wb.2.1)
    have deficitUpper : 1-W.c≤W.s^2 := by
      nlinarith only [deficit,wn.2.2]
    have large : W.c/4<W.s := by
      by_contra no
      have bound := mul_nonneg
        (show 0≤W.c/4-W.s by linarith only [no])
        (show 0≤W.c/4+W.s by linarith only [wc,wn.1])
      have correction := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
      have square := sq_pos_of_pos wc
      nlinarith only [necessary,deficitUpper,bound,correction,square]
    have outLowerU : W.loU<(4/5)*W.c+3*W.s := by
      linarith only [marker.1,large,wc]
    have outLowerV : W.loV<3*W.c-(4/5)*W.s := by
      linarith only [marker.2.2.1,wc,wn.1]
    by_cases outU : W.loU+W.side≤(4/5)*W.c+3*W.s
    · have farLower : (187/100)*W.c-(19/25)*W.s≤W.loV := by
        apply le_of_not_gt
        intro no
        have farU : (19/25)*W.c+(187/100)*W.s≤W.loU := by
          apply le_of_not_gt
          intro inU
          apply missingFar
          refine ⟨(by linarith only [inU]), ?_, (by linarith only [no]), ?_⟩ <;>
            linarith only [marker.2.1,high.2.2.2,wc,wn.1,wn.2.1]
        have short : (1/25)*W.c+(113/100)*W.s<1 := by
          linarith only [wn.2.1,wb.2.2.2.2.2]
        linarith only [farU,outU,side,short]
      have lowFarWeighted := mul_nonneg wn.1 (sub_nonneg.mpr farLower)
      have outWeighted := mul_nonneg wc.le (sub_nonneg.mpr outU)
      have sum := sum_margin wn
      have dot : W.c*W.s≤1/2 := by
        nlinarith only [wn.2.2,sq_nonneg (W.c-W.s)]
      exfalso
      nlinarith only [wall,width,lowFarWeighted,outWeighted,sum,dot,
        wn.2.2,sq_nonneg W.s]
    · have outV : W.loV+W.side≤3*W.c-(4/5)*W.s := by
        apply le_of_not_gt
        intro upper
        apply missingOut
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          linarith only [outLowerU, lt_of_not_ge outU, outLowerV, upper]
      have span : 1<W.c+W.s/5 := by linarith only [lower,outV,side]
      have product := mul_pos (sub_pos.mpr span)
        (show 0<W.c+1 by linarith only [wc])
      have correction := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
      have small : W.s<2/5 := by
        nlinarith only [product,correction,wn.2.2,wn.1]
      have squareBound := mul_pos (sub_pos.mpr small)
        (show 0<2/5+W.s by linarith only [wn.1])
      have wide : 21/25<W.c^2 := by
        nlinarith only [squareBound,wn.2.2]
      have upperDeficit := mul_pos (sub_pos.mpr span)
        (show 0<1-W.s by linarith only [small])
      have quadratic := sq_nonneg (W.s-1/2)
      exfalso
      nlinarith only [necessary,upperDeficit,quadratic,wide]
  · exact capV

/-- The two genuine faces force a strictly positive wall sine below
0.172. The proof includes the zero-angle endpoint. -/
theorem tilt {d t a lo : ℝ} (wn : Normal d t) (side : 1<a)
    (lower : 2*d-t≤lo) (upper : lo+a≤3*d-(457/500)*t) :
    0<t ∧ t<43/250 := by
  have wb := normal_bounds wn
  have span : 1<d+(43/500)*t := by linarith only [side,lower,upper]
  have positive : 0<t := by linarith only [span,wb.2.1]
  have product := mul_pos (sub_pos.mpr span)
    (show 0<d+1 by linarith only [wb.1])
  have correction := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
  have small : t<43/250 := by
    nlinarith only [product,correction,wn.2.2,positive]
  exact ⟨positive,small⟩

#print axioms upper_v
#print axioms tilt
end N12Compact.PositiveWallOwnedWestFaces
