import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Continuous support margins for the actual southwest central square.
Each expression is linear in the test normal. Its two cone endpoints
suffice; the endpoint inequalities are exact polynomial identities.
No angle subdivision or numerical certificate is used. -/
namespace N12Compact.C868CentralMargins

open C977CornerCubic
set_option Elab.async false

private theorem sum_bound {C S : ℝ} (h : Normal C S) :
    C+S ≤ 17/12 := by
  nlinarith only [h.2.2,sq_nonneg (C-S),sq_nonneg (C+S-17/12)]

private theorem endpointI {C S : ℝ} (h : Normal C S) :
    0 ≤ 1-(1/20)*C-(27/20)*S := by
  have b := sum_bound h
  linarith only [b,h.2.1]

private theorem endpointIII {C S : ℝ} (h : Normal C S) :
    0 ≤ 1-(13/20)*C-(3/4)*S := by
  have b := sum_bound h
  linarith only [b,h.2.1]

/-- A linear functional is nonnegative throughout the cone between
the canonical normal (C,S) and the diagonal. -/
private theorem cone_above {c s C S p q : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0 ≤ s*C-c*S)
    (atNormal : 0 ≤ C*p+S*q) (atDiagonal : 0 ≤ p+q) :
    0 ≤ c*p+s*q := by
  have cb := normal_bounds hn
  have cbig := normal_bounds h
  by_cases equal : C=S
  · have same : c=s := by
      have product := mul_nonneg (show 0≤c-s by linarith only [hn.2.1])
        (show 0≤C by linarith only [cbig.1])
      rw [← equal] at order
      nlinarith only [order,hn.2.1,cbig.1]
    rw [same]
    nlinarith only [mul_nonneg hn.1 atDiagonal]
  · have gap : 0<C-S := by
      have strict : S<C := lt_of_le_of_ne h.2.1 (Ne.symm equal)
      linarith only [strict]
    have first := mul_nonneg (sub_nonneg.mpr hn.2.1) atNormal
    have second := mul_nonneg order atDiagonal
    have identity : (C-S)*(c*p+s*q) =
        (c-s)*(C*p+S*q)+(s*C-c*S)*(p+q) := by ring
    exact nonneg_of_mul_nonneg_right
      (by linarith only [identity,first,second]) gap

/-- The other cone has endpoints the horizontal normal and (C,S). -/
private theorem cone_below {c s C S p q : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0 ≤ c*S-s*C)
    (atNormal : 0 ≤ C*p+S*q) (atAxis : 0 ≤ p) :
    0 ≤ c*p+s*q := by
  have cb := normal_bounds hn
  have cbig := normal_bounds h
  by_cases zero : S=0
  · have small : s=0 := by
      rw [zero] at order
      nlinarith only [order,hn.1,cbig.1]
    rw [small]
    nlinarith only [mul_nonneg (show 0≤c by linarith only [cb.1]) atAxis]
  · have positive : 0<S := lt_of_le_of_ne h.1 (Ne.symm zero)
    have first := mul_nonneg hn.1 atNormal
    have second := mul_nonneg order atAxis
    have identity : S*(c*p+s*q) = s*(C*p+S*q)+(c*S-s*C)*p := by ring
    exact nonneg_of_mul_nonneg_right
      (by linarith only [identity,first,second]) positive

private theorem margin_above {c s C S U V : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0 ≤ s*C-c*S)
    (atNormal : 0 ≤ U-(33/20)*C-(47/20)*S)
    (atDiagonal : 0 ≤ (C+S)*U+(C-S)*V-4) :
    0 ≤ (c*C+s*S)*U+(s*C-c*S)*V-(33/20)*c-(47/20)*s := by
  let p := C*U-S*V-33/20
  let q := S*U+C*V-47/20
  have normal : C*p+S*q=U-(33/20)*C-(47/20)*S := by
    dsimp [p,q]
    linear_combination U*h.2.2
  have diagonal : p+q=(C+S)*U+(C-S)*V-4 := by dsimp [p,q]; ring
  have result := cone_above hn h order
    (show 0≤C*p+S*q by rw [normal]; exact atNormal)
    (show 0≤p+q by rw [diagonal]; exact atDiagonal)
  dsimp [p,q] at result
  nlinarith only [result]

private theorem margin_below {c s C S U V : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : s*C-c*S ≤ 0)
    (atNormal : 0 ≤ U-(33/20)*C-(47/20)*S)
    (atAxis : 0 ≤ C*U-S*V-33/20) :
    0 ≤ (c*C+s*S)*U+(s*C-c*S)*V-(33/20)*c-(47/20)*s := by
  let p := C*U-S*V-33/20
  let q := S*U+C*V-47/20
  have normal : C*p+S*q=U-(33/20)*C-(47/20)*S := by
    dsimp [p,q]
    linear_combination U*h.2.2
  have result := cone_below hn h
    (show 0≤c*S-s*C by linarith only [order])
    (show 0≤C*p+S*q by rw [normal]; exact atNormal) atAxis
  dsimp [p,q] at result
  nlinarith only [result]

theorem modeI_nonneg {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : 0 ≤ s*C-c*S) :
    0 ≤ (c*C+s*S)*(1+(8/5)*C+S)+(s*C-c*S)*(2*C-(87/50)*S)-
      (33/20)*c-(47/20)*s := by
  apply margin_above hn h order
  · linarith only [endpointI h]
  · have b := normal_bounds h
    have upper := sum_bound h
    have chord := mul_nonneg (show 0≤C+S-1 by linarith only [b.2.2.2.2.1])
      (show 0≤17/12-(C+S) by linarith only [upper])
    have curve : 0≤3/5+(C+S)-(C+S)^2 := by
      nlinarith only [chord,upper]
    have correction := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
    have identity : (C+S)*(1+(8/5)*C+S)+(C-S)*(2*C-(87/50)*S)-4 =
        3/5+(C+S)-(C+S)^2+(43/50)*S*(C-S) := by
      linear_combination (23/5)*h.2.2
    nlinarith only [identity,curve,correction]

theorem modeI_nonpos {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : s*C-c*S ≤ 0) :
    0 ≤ (c*C+s*S)*(1+(8/5)*C+S)+(s*C-c*S)*((87/50)*C-2*S)-
      (33/20)*c-(47/20)*s := by
  apply margin_below hn h order
  · linarith only [endpointI h]
  · have b := normal_bounds h
    have half : C*S≤1/2 := by nlinarith only [h.2.2,sq_nonneg (C-S)]
    have identity : C*(1+(8/5)*C+S)-S*((87/50)*C-2*S)-33/20 =
        C-1/20+(2/5)*S^2-(37/50)*C*S := by
      linear_combination (8/5)*h.2.2
    nlinarith only [identity,b.1,half,sq_nonneg S]

theorem modeII_nonneg {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : 0 ≤ s*C-c*S) (shallow : 13*S≤C) :
    0 ≤ (c*C+s*S)*(2*C+(87/50)*S)+(s*C-c*S)*(1+(8/5)*C-S)-
      (33/20)*c-(47/20)*s := by
  have b := normal_bounds h
  apply margin_above hn h order
  · linarith only [shallow,b.1]
  · have small : S≤1/13 := by linarith only [shallow,b.2.1]
    have sqBound := mul_nonneg h.1 (show 0≤1-S by linarith only [small])
    have positive := mul_nonneg (show 0≤C by linarith only [b.1]) h.1
    have identity : (C+S)*(2*C+(87/50)*S)+(C-S)*(1+(8/5)*C-S)-4 =
        C-S-2/5-(43/50)*S^2+(57/50)*C*S := by
      linear_combination (18/5)*h.2.2
    nlinarith only [identity,b.1,small,sqBound,positive]

theorem modeIII_nonneg {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : 0 ≤ s*C-c*S) :
    0 ≤ (c*C+s*S)*(1+C+(8/5)*S)+(s*C-c*S)*(1+C-(8/5)*S)-
      (33/20)*c-(47/20)*s := by
  apply margin_above hn h order
  · linarith only [endpointIII h]
  · have b := normal_bounds h
    have product := mul_nonneg (show 0≤1-C by linarith only [b.2.1])
      (show 0≤3*C-2 by linarith only [b.1])
    have identity : (C+S)*(1+C+(8/5)*S)+(C-S)*(1+C-(8/5)*S)-4 =
        (2/5)*(1-C)*(3*C-2) := by
      linear_combination (16/5)*h.2.2
    nlinarith only [identity,product]

theorem modeIII_nonpos {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : s*C-c*S ≤ 0) :
    0 ≤ (c*C+s*S)*(1+C+(8/5)*S)+(s*C-c*S)*((87/50)*C-2*S)-
      (33/20)*c-(47/20)*s := by
  apply margin_below hn h order
  · linarith only [endpointIII h]
  · have b := normal_bounds h
    have half : C*S≤1/2 := by nlinarith only [h.2.2,sq_nonneg (C-S)]
    have product := mul_nonneg (show 0≤C by linarith only [b.1])
      (show 0≤1-C by linarith only [b.2.1])
    have identity : C*(1+C+(8/5)*S)-S*((87/50)*C-2*S)-33/20 =
        C-13/20+S^2-(7/50)*C*S := by linear_combination h.2.2
    nlinarith only [identity,product,half,h.2.2]

end N12Compact.C868CentralMargins
