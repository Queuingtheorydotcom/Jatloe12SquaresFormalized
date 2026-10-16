import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Scalar endgame for the positive-B / upper-U-C sector of849/851.
The stronger height bound comes from the actual upper-left owner's (1,3).
The cap is supplied by C's actual forced point (2.086,3). These are not the
old template's corner premises. Geometry-to-scalar binding remains separate.
-/
namespace N12Compact.C849PositiveSupport

private theorem canonical_bounds (C S : ℝ)
    (hc : 0 < C) (hs : |S| ≤ C) (unit : C^2+S^2=1) :
    7/10 ≤ C ∧ C ≤ 1 ∧ |S| ≤ 71/100 ∧ 1-(3/5)*S^2 ≤ C := by
  have square := (sq_le_sq₀ (abs_nonneg S) hc.le).mpr hs
  rw [sq_abs] at square
  have cLow : 7/10 ≤ C := by
    nlinarith only [unit,square,hc,sq_nonneg (C-7/10)]
  have cHigh : C ≤ 1 := by nlinarith only [unit,sq_nonneg S]
  have sHigh : |S| ≤ 71/100 := by
    nlinarith only [unit,square,sq_abs S,sq_nonneg (|S|-71/100)]
  have factor := mul_nonneg (sub_nonneg.mpr cHigh)
    (show 0 ≤ (3/5)*C-2/5 by linarith only [cLow])
  exact ⟨cLow,cHigh,sHigh,by nlinarith only [unit,factor]⟩

private theorem positive_margin (C S : ℝ)
    (hc : 0 < C) (hs : 0 ≤ S) (hsc : S ≤ C)
    (unit : C^2+S^2=1) :
    0 < C-9/10+(7/50)*S^2+S-(53/50)*C*S := by
  obtain ⟨_,_,sBound,cBound⟩ := canonical_bounds C S hc
    (by simpa only [abs_of_nonneg hs] using hsc) unit
  rw [abs_of_nonneg hs] at sBound
  have product := mul_nonneg (sub_nonneg.mpr cBound)
    (show 0 ≤ 1-(53/50)*S by linarith only [sBound])
  let z := S-1/2
  have cubic := mul_nonneg (sq_nonneg z)
    (show 0 ≤ z+1/2 by dsimp [z]; linarith only [hs])
  have square := sq_nonneg (352*z-43)
  dsimp [z] at cubic square
  nlinarith only [product,cubic,square]

private theorem negative_margin (C S : ℝ)
    (hc : 0 < C) (hs : S ≤ 0) (hsc : |S| ≤ C)
    (unit : C^2+S^2=1) :
    0 < C-9/10-(17/25)*C*S-(7/500)*S^2 := by
  obtain ⟨cLow,_,sBound,cBound⟩ := canonical_bounds C S hc hsc unit
  rw [abs_of_nonpos hs] at sBound
  have product := mul_nonneg (sub_nonneg.mpr cLow) (neg_nonneg.mpr hs)
  have square := mul_nonneg (neg_nonneg.mpr hs)
    (show 0 ≤ 71/100+S by linarith only [sBound])
  nlinarith only [cBound,product,square]

private theorem steep_margin (C S : ℝ)
    (hc : 0 < C) (hs : 3/5 ≤ S) (hsc : S ≤ C)
    (unit : C^2+S^2=1) :
    0 < C-1543/1000+(783/1000)*S^2+S-(13/50)*C*S := by
  have sNonneg : 0 ≤ S := by linarith only [hs]
  obtain ⟨_,_,sBound,cBound⟩ := canonical_bounds C S hc
    (by simpa only [abs_of_nonneg sNonneg] using hsc) unit
  rw [abs_of_nonneg sNonneg] at sBound
  have product := mul_nonneg (sub_nonneg.mpr cBound)
    (show 0 ≤ 1-(13/50)*S by linarith only [sBound])
  have square := mul_nonneg (sub_nonneg.mpr hs)
    (show 0 ≤ S+3/5 by linarith only [hs])
  have cubic := mul_nonneg (sq_nonneg S) (sub_nonneg.mpr hs)
  nlinarith only [product,square,cubic,hs]

/-- The L-longitudinal separator is impossible in all signed canonical L
frames, once B's new height inequality has forced 3c/4<s.
The wall/cap hypotheses have merely replaced the common side a>1 by1.
Every coefficient is retained explicitly for original-square binding. -/
theorem l_axis_impossible (c s C S U : ℝ)
    (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hC : 0 < C) (hSC : |S| ≤ C)
    (unit : c^2+s^2=1) (unitL : C^2+S^2=1)
    (steep : 3*c/4 < s)
    (wallPos : 0 ≤ S → 1+S/C+(187/100)*S-(19/25)*S^2/C ≤ U)
    (wallNeg : S ≤ 0 → 1-(457/500)*S^2/C+2*S ≤ U)
    (capPos : 0 ≤ c*S-s*C →
      U ≤ C*(1+(543/500)*c^2-c+s)+S*(3+(543/500)*c*s-c-s))
    (capNeg : c*S-s*C ≤ 0 →
      U ≤ C*(2+(43/500)*c^2+c*s/2-c-s)+
        S*(5/2+s^2/2+(43/500)*c*s+c-s)) : False := by
  have coneSquare := mul_pos (sub_pos.mpr steep)
    (show 0 < s+3*c/4 by linarith only [hc,hs])
  have cBound : c ≤ 4/5 := by
    nlinarith only [unit,coneSquare,sq_nonneg (c-4/5)]
  have sBound : 3/5 ≤ s := by
    nlinarith only [unit,coneSquare,hs,sq_nonneg (s-3/5)]
  have hBound : c-s ≤ 1/5 := by linarith only [steep,cBound]
  have sumLow : 7/5 ≤ c+s := by
    have square := mul_nonneg
      (show 0 ≤ 1/5-(c-s) by linarith only [hBound])
      (show 0 ≤ 1/5+(c-s) by linarith only [hsc])
    nlinarith only [unit,square,hc,hs,sq_nonneg (c+s-7/5)]
  have sumHigh : c+s ≤ 283/200 := by
    nlinarith only [unit,sq_nonneg (c-s),sq_nonneg (c+s-283/200)]
  have csNonneg := mul_nonneg hc.le hs
  have posA : 1+(543/500)*c^2-c+s ≤ 1543/1000 := by
    have product := mul_nonneg (sub_nonneg.mpr hsc)
      (show 0 ≤ 1-(543/1000)*(c+s) by linarith only [sumHigh])
    nlinarith only [unit,product]
  have posB : 3+(543/500)*c*s-c-s ≤ 213/100 := by
    have product := mul_nonneg (sub_nonneg.mpr sumHigh)
      (show 0 ≤ (543/1000)*(c+s+283/200)-1 by linarith only [sumLow])
    nlinarith only [unit,product]
  have negA : 2+(43/500)*c^2+c*s/2-c-s ≤ 9/10 := by
    have cSquare := mul_nonneg (sub_nonneg.mpr cBound)
      (show 0 ≤ 4/5+c by linarith only [hc])
    have sumSquare := mul_nonneg (sub_nonneg.mpr sumLow)
      (show 0 ≤ 13/5-(c+s) by linarith only [sumHigh])
    nlinarith only [unit,cSquare,sumSquare]
  have negBHigh : 5/2+s^2/2+(43/500)*c*s+c-s ≤ 293/100 := by
    have product := mul_nonneg (sub_nonneg.mpr hsc) (sub_nonneg.mpr sumLow)
    nlinarith only [unit,product,hBound,sq_nonneg (c-s)]
  have negBLow : 67/25 ≤ 5/2+s^2/2+(43/500)*c*s+c-s := by
    have square := mul_nonneg (sub_nonneg.mpr sBound)
      (show 0 ≤ s+3/5 by linarith only [hs])
    nlinarith only [square,csNonneg,hsc]
  by_cases cross : 0 ≤ c*S-s*C
  · have transferred := mul_pos
      (show 0 < 4*s-3*c by linarith only [steep]) hC
    have slope : 3*C < 4*S := by
      by_contra bad
      have product := mul_nonneg hc.le
        (show 0 ≤ 3*C-4*S by linarith only [le_of_not_gt bad])
      nlinarith only [transferred,product,cross]
    have sPos : 0 ≤ S := by linarith only [slope,hC]
    have square := mul_pos (sub_pos.mpr slope)
      (show 0 < 4*S+3*C by linarith only [hC,sPos])
    have sLow : 3/5 ≤ S := by
      nlinarith only [unitL,square,sPos,sq_nonneg (S-3/5)]
    have first := mul_le_mul_of_nonneg_left posA hC.le
    have second := mul_le_mul_of_nonneg_left posB sPos
    have cap : U ≤ (1543/1000)*C+(213/100)*S := by
      nlinarith only [capPos cross,first,second]
    have clear : (1+S/C+(187/100)*S-(19/25)*S^2/C)*C =
        C+S+(187/100)*S*C-(19/25)*S^2 := by
      field_simp [ne_of_gt hC]
    have wall := mul_le_mul_of_nonneg_right (wallPos sPos) hC.le
    rw [clear] at wall
    have scaled := mul_le_mul_of_nonneg_right cap hC.le
    have margin := steep_margin C S hC sLow (abs_le.mp hSC).2 unitL
    nlinarith only [wall,scaled,unitL,margin]
  · have cross' : c*S-s*C ≤ 0 := le_of_not_ge cross
    have first := mul_le_mul_of_nonneg_left negA hC.le
    by_cases sign : 0 ≤ S
    · have second := mul_le_mul_of_nonneg_left negBHigh sign
      have cap : U ≤ (9/10)*C+(293/100)*S := by
        nlinarith only [capNeg cross',first,second]
      have clear : (1+S/C+(187/100)*S-(19/25)*S^2/C)*C =
          C+S+(187/100)*S*C-(19/25)*S^2 := by
        field_simp [ne_of_gt hC]
      have wall := mul_le_mul_of_nonneg_right (wallPos sign) hC.le
      rw [clear] at wall
      have scaled := mul_le_mul_of_nonneg_right cap hC.le
      have margin := positive_margin C S hC sign (abs_le.mp hSC).2 unitL
      nlinarith only [wall,scaled,unitL,margin]
    · have sign' : S ≤ 0 := le_of_not_ge sign
      have second := mul_le_mul_of_nonpos_left negBLow sign'
      have cap : U ≤ (9/10)*C+(67/25)*S := by
        nlinarith only [capNeg cross',first,second]
      have clear : (1-(457/500)*S^2/C+2*S)*C =
          C-(457/500)*S^2+2*S*C := by
        field_simp [ne_of_gt hC]
      have wall := mul_le_mul_of_nonneg_right (wallNeg sign') hC.le
      rw [clear] at wall
      have scaled := mul_le_mul_of_nonneg_right cap hC.le
      have margin := negative_margin C S hC sign' hSC unitL
      nlinarith only [wall,scaled,unitL,margin]

#print axioms l_axis_impossible
end N12Compact.C849PositiveSupport
