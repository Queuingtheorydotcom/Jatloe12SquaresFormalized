import Compact.Geometry.C849NegativePositiveMargins
import Compact.Geometry.C849NegativeLeftScalar
import Compact.Geometry.C849NegativeBL

/-! Original-square realization of the two signed-L scalar support bounds.
All position caps are the original point faces; the corner cap is obtained
from the actual equal-side corner square by C849NegativeCorner. -/
namespace N12Compact.C849NegativeLongitudinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

private theorem positive_scalar (a c t C S U V W : ℝ)
    (ha : 1 < a) (hc : 0 < c) (ht : 0 ≤ t) (order : t ≤ c)
    (unit : c^2+t^2=1) (hC : 0 < C) (hS : 0 ≤ S) (sC : S ≤ C)
    (unitL : C^2+S^2=1)
    (wall : a*(C+S)+(187/100)*C*S-(19/25)*S^2 ≤ C*W)
    (aCap : U+a ≤ 2*c-(5/2)*t)
    (bottom : V ≤ (33/20)*t+(47/20)*c)
    (corner : a*(c+t)-4*t ≤ U)
    (cFace : U+a ≤ (113/50)*c-3*t ∨ V+a ≤ (113/50)*t+3*c)
    (axis : W ≤ (c*C-t*S)*U+(t*C+c*S)*V) : False := by
  have g : 0 ≤ c*C-t*S := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr order) hC.le,
      mul_nonneg ht (sub_nonneg.mpr sC)]
  have k : 0 ≤ t*C+c*S := by positivity
  have scaled := mul_le_mul_of_nonneg_left axis hC.le
  have aScaled := mul_le_mul_of_nonneg_left aCap (mul_nonneg hC.le g)
  have bottomScaled := mul_le_mul_of_nonneg_left bottom (mul_nonneg hC.le k)
  have normalC := congrArg (fun z : ℝ => C^2*z) unit
  have normalS := congrArg (fun z : ℝ => C*S*z) unit
  dsimp only at normalC normalS
  rcases cFace with cU | cV
  · have gain := mul_pos (sub_pos.mpr ha)
      (show 0 < 1+c+t by positivity)
    have cLower : 50/63 ≤ c := by nlinarith only [corner,cU,gain]
    have margin := C849NegativePositiveMargins.upperU c t C S hc ht unit order hC hS unitL sC cLower
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < C*(c*C-t*S)+C+S by positivity)
    rcases margin with margin | margin
    · unfold C849NegativePositiveMargins.margin0 at margin
      nlinarith only [scaled,aScaled,bottomScaled,wall,strict,margin,normalC,normalS]
    · unfold C849NegativePositiveMargins.margin1 at margin
      have cScaled := mul_le_mul_of_nonneg_left cU (mul_nonneg hC.le g)
      nlinarith only [scaled,cScaled,bottomScaled,wall,strict,margin,normalC,normalS]
  · have margin := C849NegativePositiveMargins.upperV c t C S hc ht unit order hC hS unitL sC
    unfold C849NegativePositiveMargins.margin2 at margin
    have cScaled := mul_le_mul_of_nonneg_left cV (mul_nonneg hC.le k)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < C*((c*C-t*S)+(t*C+c*S))+C+S by positivity)
    nlinarith only [scaled,aScaled,cScaled,wall,strict,margin,normalC,normalS]

theorem impossible (B L : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < B.side) (same : B.side=L.side)
    (box : InsideContainer L) (left : ClosedInside L (457/500) 2)
    (low : -L.s*(19/25)+L.c*(187/100) ≤ L.loV)
    (aCap : B.loU+B.side ≤ 2*B.c+(5/2)*B.s)
    (bottom : B.Inside (33/20) (47/20))
    (high : B.Inside 2 (1543/500))
    (corner : B.side*(B.c-B.s)+4*B.s ≤ B.loU)
    (cFace : B.loU+B.side ≤ (113/50)*B.c+3*B.s ∨
      B.loV+B.side ≤ -(113/50)*B.s+3*B.c)
    (axis : L.loU+L.side ≤ lower B L.c L.s) : False := by
  let c := B.c
  let t := -B.s
  let C := L.c
  let S := L.s
  have ht : 0 ≤ t := neg_nonneg.mpr bs
  have normal : c^2+t^2=1 := by dsimp [c,t]; nlinarith only [B.unit_normal]
  have g : 0 ≤ B.c*L.c+B.s*L.s := by
    have sum : 0 ≤ L.c+L.s := by linarith only [(abs_le.mp lsc).1]
    have first := mul_nonneg (show 0 ≤ B.c+B.s by linarith only [bsc]) lc.le
    have second := mul_nonneg (neg_nonneg.mpr bs) (show 0 ≤ L.c-L.s by linarith only [(abs_le.mp lsc).2])
    nlinarith only [first,second]
  have minimum := FourSquareBLBridge.minimum_projection B L g
  change L.loU+L.side ≤ L.c*centerX B+L.s*centerY B-supportRadius B L.c L.s at axis
  rw [minimum] at axis
  have bounds := FourSquareBLBridge.left_upper_bounds L lc box left low
  have corner' : B.side*(c+t)-4*t ≤ B.loU := by dsimp [c,t]; nlinarith only [corner]
  have aCap' : B.loU+B.side ≤ 2*c-(5/2)*t := by dsimp [c,t]; linarith only [aCap]
  have bottom' : B.loV ≤ (33/20)*t+(47/20)*c := by
    dsimp [c,t]; linarith only [bottom.2.2.1]
  have high' : 2*t+(1543/500)*c ≤ B.loV+B.side := by
    dsimp [c,t]; linarith only [high.2.2.2]
  have cFace' : B.loU+B.side ≤ (113/50)*c-3*t ∨ B.loV+B.side ≤ (113/50)*t+3*c := by
    dsimp [c,t]
    rcases cFace with h | h
    · left; linarith only [h]
    · right; linarith only [h]
  by_cases sign : 0 ≤ L.s
  · have k : 0 ≤ B.c*L.s-B.s*L.c := by
      nlinarith only [mul_nonneg bc.le sign,mul_nonpos_of_nonpos_of_nonneg bs lc.le]
    rw [abs_of_nonneg k] at axis
    have wall := mul_le_mul_of_nonneg_right (bounds.1 sign) lc.le
    have clear : (L.side*(1+L.s/L.c)+(187/100)*L.s-(19/25)*L.s^2/L.c)*L.c =
        L.side*(L.c+L.s)+(187/100)*L.c*L.s-(19/25)*L.s^2 := by
      field_simp [ne_of_gt lc] <;> ring
    rw [clear] at wall
    have wall' : B.side*(C+S)+(187/100)*C*S-(19/25)*S^2 ≤ C*(L.loU+L.side) := by
      dsimp [C,S]
      rw [same]
      nlinarith only [wall]
    apply positive_scalar B.side c t C S B.loU B.loV (L.loU+L.side)
      ha bc ht bsc normal lc sign (abs_le.mp lsc).2 L.unit_normal wall' aCap'
      bottom' corner' cFace'
    dsimp [c,t,C,S]
    nlinarith only [axis]
  · have sign' := le_of_not_ge sign
    have wall := mul_le_mul_of_nonneg_right (bounds.2 sign') lc.le
    have clear : (L.side-(457/500)*L.s^2/L.c+2*L.s)*L.c =
        L.side*L.c-(457/500)*L.s^2+2*L.c*L.s := by
      field_simp [ne_of_gt lc] <;> ring
    rw [clear] at wall
    have wall' : B.side*C-(457/500)*(-S)^2-2*C*(-S) ≤ C*(L.loU+L.side) := by
      dsimp [C,S]
      rw [same]
      nlinarith only [wall]
    apply C849NegativeLeftScalar.impossible B.side c t C (-S) B.loU B.loV (L.loU+L.side)
      ha bc ht bsc normal lc (neg_nonneg.mpr sign') (by dsimp [S,C]; linarith only [(abs_le.mp lsc).1])
      (by dsimp [C,S]; nlinarith only [L.unit_normal])
      wall' aCap' bottom' high' cFace'
    have coefficient : c*C+t*(-S)=B.c*L.c+B.s*L.s := by dsimp [c,t,C,S]; ring
    have angle : t*C-c*(-S)=B.c*L.s-B.s*L.c := by dsimp [c,t,C,S]; ring
    rw [coefficient,angle]
    exact axis

#print axioms impossible
end N12Compact.C849NegativeLongitudinal
