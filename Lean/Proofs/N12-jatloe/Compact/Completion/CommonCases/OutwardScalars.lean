import Compact.Completion.CommonCases.CanonicalScalars

namespace N12Compact.CommonCases.OutwardScalars
set_option Elab.async false

theorem increasing_projection (c s a b : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (an : 0 ≤ a) (ab : a ≤ b)
    (small : (a+b)*(99/140) < 1) : a*c+b*s < 1 := by
  have sum : c+s < 99/70 := by nlinarith only [unit,sq_nonneg (c-s),cp,sn]
  have diff := mul_nonneg (sub_nonneg.mpr ab) (sub_nonneg.mpr order)
  have high := mul_nonneg (show 0 ≤ a+b by linarith only [an,ab])
    (show 0 ≤ 99/70-(c+s) by linarith only [sum])
  nlinarith only [diff,high,small]

/-- The half-angle cutoff is derived from the actual same-face span.
No independently optimized support bound is substituted. -/
theorem shallow_projection (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (span : 1 < c+(143/500)*s) : (27/50)*c+(101/100)*s < 1 := by
  have one : c ≤ 1 := (CanonicalScalars.bounds c s cp sp.le order unit).2.1
  have product := mul_lt_mul_of_pos_right
    (show 1-c < (143/500)*s by linarith only [span])
    (show 0 < 1+c by linarith only [cp])
  have scaled : s^2 < (143/500)*s*(1+c) := by nlinarith only [product,unit]
  have half : s < (143/500)*(1+c) := by
    have h := (mul_lt_mul_iff_right₀ sp).mp (show s*s < s*((143/500)*(1+c)) by
      nlinarith only [scaled])
    exact h
  let c0 : ℝ := 229551/270449
  let s0 : ℝ := 143000/270449
  have unit0 : c0^2+s0^2=1 := by norm_num [c0,s0]
  have cp0 : 0 < c0 := by norm_num [c0]
  have sp0 : 0 < s0 := by norm_num [s0]
  have order0 : s0 ≤ c0 := by norm_num [c0,s0]
  have boundary : s0=(143/500)*(1+c0) := by norm_num [c0,s0]
  have sBound : s ≤ s0 := by
    by_contra failed
    have high : s0 < s := lt_of_not_ge failed
    have cBound : c < c0 := by
      dsimp [c0,s0] at *
      nlinarith only [unit,cp,high,sp]
    rw [boundary] at high
    dsimp [c0] at high cBound
    nlinarith only [high,half,cBound]
  have cBound : c0 ≤ c := by
    dsimp [c0,s0] at *
    nlinarith only [unit,cp,sBound,sp]
  have diff := mul_nonneg (sub_nonneg.mpr cBound)
    (show 0 ≤ (c+c0)-(s+s0) by linarith only [order,order0])
  have scaledSum : 0 ≤ (c0+s0-c-s)*(s+s0) := by
    dsimp [c0,s0] at diff unit0 ⊢
    nlinarith only [diff,unit,unit0]
  have sumBound : c+s ≤ c0+s0 := by
    have h := nonneg_of_mul_nonneg_left scaledSum
      (show 0 < s+s0 by linarith only [sp,sp0])
    linarith only [h]
  have wSum := mul_nonneg (by norm_num : (0:ℝ) ≤ 27/50) (sub_nonneg.mpr sumBound)
  have wSine := mul_nonneg (by norm_num : (0:ℝ) ≤ 47/100) (sub_nonneg.mpr sBound)
  have evaluation : (27/50)*c0+(101/100)*s0 < 1 := by norm_num [c0,s0]
  dsimp [c0,s0] at wSum wSine evaluation
  nlinarith only [wSum,wSine,evaluation]

theorem short_strong_projection (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (span : 1 < c+(89/250)*s) : (23/50)*c+(101/100)*s < 1 := by
  have one : c ≤ 1 := (CanonicalScalars.bounds c s cp sp.le order unit).2.1
  have product := mul_lt_mul_of_pos_right
    (show 1-c < (89/250)*s by linarith only [span])
    (show 0 < 1+c by linarith only [cp])
  have scaled : s^2 < (89/250)*s*(1+c) := by nlinarith only [product,unit]
  have half : s < (89/250)*(1+c) := by
    have h := (mul_lt_mul_iff_right₀ sp).mp (show s*s < s*((89/250)*(1+c)) by
      nlinarith only [scaled])
    exact h
  let c0 : ℝ := 54579/70421
  let s0 : ℝ := 44500/70421
  have unit0 : c0^2+s0^2=1 := by norm_num [c0,s0]
  have cp0 : 0 < c0 := by norm_num [c0]
  have sp0 : 0 < s0 := by norm_num [s0]
  have order0 : s0 ≤ c0 := by norm_num [c0,s0]
  have boundary : s0=(89/250)*(1+c0) := by norm_num [c0,s0]
  have sBound : s ≤ s0 := by
    by_contra failed
    have high : s0 < s := lt_of_not_ge failed
    have cBound : c < c0 := by
      dsimp [c0,s0] at *
      nlinarith only [unit,cp,high,sp]
    rw [boundary] at high
    dsimp [c0] at high cBound
    nlinarith only [high,half,cBound]
  have cBound : c0 ≤ c := by
    dsimp [c0,s0] at *
    nlinarith only [unit,cp,sBound,sp]
  have diff := mul_nonneg (sub_nonneg.mpr cBound)
    (show 0 ≤ (c+c0)-(s+s0) by linarith only [order,order0])
  have scaledSum : 0 ≤ (c0+s0-c-s)*(s+s0) := by
    dsimp [c0,s0] at diff unit0 ⊢
    nlinarith only [diff,unit,unit0]
  have sumBound : c+s ≤ c0+s0 := by
    have h := nonneg_of_mul_nonneg_left scaledSum
      (show 0 < s+s0 by linarith only [sp,sp0])
    linarith only [h]
  have wSum := mul_nonneg (by norm_num : (0:ℝ) ≤ 23/50) (sub_nonneg.mpr sumBound)
  have wSine := mul_nonneg (by norm_num : (0:ℝ) ≤ 55/100) (sub_nonneg.mpr sBound)
  have evaluation : (23/50)*c0+(101/100)*s0 < 1 := by norm_num [c0,s0]
  dsimp [c0,s0] at wSum wSine evaluation
  nlinarith only [wSum,wSine,evaluation]

theorem strong_bar_projection (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (span : 1 < c+(113/500)*s) : (313/500)*c+(101/100)*s < 1 := by
  have one : c ≤ 1 := (CanonicalScalars.bounds c s cp sp.le order unit).2.1
  have product := mul_lt_mul_of_pos_right
    (show 1-c < (113/500)*s by linarith only [span])
    (show 0 < 1+c by linarith only [cp])
  have scaled : s^2 < (113/500)*s*(1+c) := by nlinarith only [product,unit]
  have half : s < (113/500)*(1+c) := by
    have h := (mul_lt_mul_iff_right₀ sp).mp (show s*s < s*((113/500)*(1+c)) by
      nlinarith only [scaled])
    exact h
  let c0 : ℝ := 237231/262769
  let s0 : ℝ := 113000/262769
  have unit0 : c0^2+s0^2=1 := by norm_num [c0,s0]
  have cp0 : 0 < c0 := by norm_num [c0]
  have sp0 : 0 < s0 := by norm_num [s0]
  have order0 : s0 ≤ c0 := by norm_num [c0,s0]
  have boundary : s0=(113/500)*(1+c0) := by norm_num [c0,s0]
  have sBound : s ≤ s0 := by
    by_contra failed
    have high : s0 < s := lt_of_not_ge failed
    have cBound : c < c0 := by
      dsimp [c0,s0] at *
      nlinarith only [unit,cp,high,sp]
    rw [boundary] at high
    dsimp [c0] at high cBound
    nlinarith only [high,half,cBound]
  have cBound : c0 ≤ c := by
    dsimp [c0,s0] at *
    nlinarith only [unit,cp,sBound,sp]
  have diff := mul_nonneg (sub_nonneg.mpr cBound)
    (show 0 ≤ (c+c0)-(s+s0) by linarith only [order,order0])
  have scaledSum : 0 ≤ (c0+s0-c-s)*(s+s0) := by
    dsimp [c0,s0] at diff unit0 ⊢
    nlinarith only [diff,unit,unit0]
  have sumBound : c+s ≤ c0+s0 := by
    have h := nonneg_of_mul_nonneg_left scaledSum
      (show 0 < s+s0 by linarith only [sp,sp0])
    linarith only [h]
  have wSum := mul_nonneg (by norm_num : (0:ℝ) ≤ 313/500) (sub_nonneg.mpr sumBound)
  have wSine := mul_nonneg (by norm_num : (0:ℝ) ≤ 48/125) (sub_nonneg.mpr sBound)
  have evaluation : (313/500)*c0+(101/100)*s0 < 1 := by norm_num [c0,s0]
  dsimp [c0,s0] at wSum wSine evaluation
  nlinarith only [wSum,wSine,evaluation]

end N12Compact.CommonCases.OutwardScalars
