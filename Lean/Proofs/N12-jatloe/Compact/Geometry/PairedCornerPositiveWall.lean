import Compact.Geometry.PositiveWallOwnedWestCorner

/-! The positive wall's actual inward V face and its neighboring paired
corner suffice. No lower singleton or foreign far point is needed.
The complete corner square supplies the final strict vertex exclusion. -/
namespace N12Compact.PairedCornerPositiveWall

open S12 S12Pilot FourSquareAnchors ThreeSquare C977CornerCubic
set_option Elab.async false

private theorem outward_margin {d t : ℝ} (normal : Normal d t) :
    1-(1/5)*d^2+d*t≤d+t := by
  have b := normal_bounds normal
  have small : d+t-1≤(3/5)*d := by
    linarith only [normal.2.1,b.2.2.2.2.2]
  have product := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤(3/5)*d+(d+t-1) by linarith only [b.1,b.2.2.2.2.1])
  nlinarith only [product,normal.2.2,sq_nonneg d]

/-- The paired corner's outward point removes the last upper-U escape
using only the full container wall and the actual inward V bound. -/
theorem upper_v (W : OpenSquare) (wn : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside (457/500) 2)
    (lower : 2*W.c-W.s≤W.loV)
    (missingTop : ¬W.Inside (457/500) 3)
    (missingOut : ¬W.Inside (4/5) 3) :
    W.loV+W.side≤3*W.c-(457/500)*W.s := by
  have wb := normal_bounds wn
  have wc : 0<W.c := by linarith only [wb.1]
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
    · have outWeighted := mul_nonneg wc.le (sub_nonneg.mpr outU)
      have margin := outward_margin wn
      exfalso
      nlinarith only [wall,width,lowWeighted,outWeighted,margin,wn.2.2]
    · have outV : W.loV+W.side≤3*W.c-(4/5)*W.s := by
        apply le_of_not_gt
        intro upper
        apply missingOut
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [outLowerU,lt_of_not_ge outU,outLowerV,upper]
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

/-- Complete positive-wall contradiction from the actual paired corner.
The corner's orientation is arbitrary and no bottom neighbor is used. -/
theorem impossible (W E : OpenSquare) (wn : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (high : W.Inside 1 (12/5))
    (lower : 2*W.c-W.s≤W.loV)
    (outward : E.Inside (4/5) 3) (corner : E.Inside 1 3)
    (left : E.Inside (457/500) 3) (top : E.Inside 1 (1543/500))
    (apart : ∀ x y, ¬(E.Inside x y ∧ W.Inside x y)) : False := by
  have upper := upper_v W wn side box marker lower
    (fun h => apart _ _ ⟨left,h⟩) (fun h => apart _ _ ⟨outward,h⟩)
  have tilt := PositiveWallOwnedWestFaces.tilt wn side lower upper
  exact PositiveWallOwnedWestCorner.impossible W E wn side box high lower upper
    tilt.1 tilt.2 outward corner top apart

/-- Square-only horizontal transport of the complete paired-corner
contradiction. The original right square may have any negative canonical
angle, including the zero endpoint. -/
theorem negative_right_impossible (R E : OpenSquare) (t : ℝ)
    (signed : R.s=-t) (normal : Normal R.c t)
    (side : 1<R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (lower : 3*t+2*R.c≤R.loV)
    (outward : E.Inside (16/5) 3) (corner : E.Inside 3 3)
    (right : E.Inside (1543/500) 3) (top : E.Inside 3 (1543/500))
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) : False := by
  let W := turnFrame (turnFrame (pullX R))
  have wi (x y : ℝ) : W.Inside x y↔R.Inside (4-x) y := by
    dsimp only [W]
    rw [turnFrame_inside,turnFrame_inside,inside_pullX]
  have wn : Normal W.c W.s := by
    dsimp [Normal,W,turnFrame,pullX]
    rw [signed]
    simpa only [neg_neg,Normal] using normal
  have wSide : 1<W.side := by simpa only [W,turnFrame_side,pullX] using side
  have wBox : InsideContainer W := by
    intro x y h
    have b := box (4-x) y ((wi x y).mp h)
    exact ⟨by linarith only [b.2.1],by linarith only [b.1],b.2.2.1,b.2.2.2⟩
  have wMarker : W.Inside (457/500) 2 := (wi _ _).mpr (by
    convert marker using 1 <;> norm_num)
  have wHigh : W.Inside 1 (12/5) := (wi _ _).mpr (by
    convert high using 1 <;> norm_num)
  have wLower : 2*W.c-W.s≤W.loV := by
    dsimp [W,turnFrame,pullX]
    rw [signed]
    linarith only [lower]
  have eOut : (pullX E).Inside (4/5) 3 := (inside_pullX E _ _).mpr (by
    convert outward using 1 <;> norm_num)
  have eCorner : (pullX E).Inside 1 3 := (inside_pullX E _ _).mpr (by
    convert corner using 1 <;> norm_num)
  have eLeft : (pullX E).Inside (457/500) 3 := (inside_pullX E _ _).mpr (by
    convert right using 1 <;> norm_num)
  have eTop : (pullX E).Inside 1 (1543/500) := (inside_pullX E _ _).mpr (by
    convert top using 1 <;> norm_num)
  exact impossible W (pullX E) wn wSide wBox wMarker wHigh wLower
    eOut eCorner eLeft eTop
    (fun x y h => apart _ _ ⟨(inside_pullX E _ _).mp h.1,(wi x y).mp h.2⟩)

/-- Every nonpositive canonical right wall contains the inward point.
The actual paired corner removes its sole possible missing face. -/
theorem negative_right_point (R E : OpenSquare) (t : ℝ)
    (signed : R.s=-t) (normal : Normal R.c t)
    (side : 1<R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (outward : E.Inside (16/5) 3) (corner : E.Inside 3 3)
    (right : E.Inside (1543/500) 3) (top : E.Inside 3 (1543/500))
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) : R.Inside 3 2 := by
  by_contra missing
  have b := normal_bounds normal
  have lower : 3*t+2*R.c≤R.loV := by
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [low,marker.2.1,high.1,high.2.2.2,signed,normal.1,b.1]
  exact negative_right_impossible R E t signed normal side box marker high lower
    outward corner right top apart

#print axioms upper_v
#print axioms impossible
#print axioms negative_right_impossible
#print axioms negative_right_point
end N12Compact.PairedCornerPositiveWall
