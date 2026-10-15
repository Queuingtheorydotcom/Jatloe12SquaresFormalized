import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! Exact scalar support inequalities for the positive four-square branch.
All frame, wall and support premises are explicit; this module does not assume
that a numerical enclosure or a separating-axis test has been checked. -/
namespace N12Compact.FourSquareLongitudinal
set_option Elab.async false
set_option maxHeartbeats 0

private theorem canonical_bounds (C S : ℝ) (hC : 0 < C)
    (hS : |S| ≤ C) (hu : C^2 + S^2 = 1) :
    7/10 ≤ C ∧ C ≤ 1 ∧ |S| ≤ 1 ∧ C ≥ 1-(3/5)*S^2 := by
  have hsq : |S|^2 ≤ C^2 := (sq_le_sq₀ (abs_nonneg S) hC.le).mpr hS
  have habs : |S|^2 = S^2 := sq_abs S
  have hC1 : C ≤ 1 := by nlinarith [sq_nonneg S]
  have hC7 : 7/10 ≤ C := by nlinarith [sq_nonneg (C-7/10)]
  have hp := mul_nonneg (sub_nonneg.mpr hC1)
    (show 0 ≤ (3/5)*C-2/5 by linarith)
  exact ⟨hC7, hC1, hS.trans hC1, by nlinarith⟩

/-- The rational margin controlling positive canonical support directions. -/
theorem positive_slope_margin (C S : ℝ) (hC : 0 < C)
    (hS0 : 0 ≤ S) (hSC : S ≤ C) (hu : C^2 + S^2 = 1) :
    0 < (1-(19/25)*S)*(1+C)+S*C-(24/25)*C*(1+C) := by
  obtain ⟨hC7,hC1,hS1,hCb⟩ :=
    canonical_bounds C S hC (by simpa [abs_of_nonneg hS0] using hSC) hu
  rw [abs_of_nonneg hS0] at hS1
  have hp := mul_nonneg (show 0 ≤ C-1+(3/5)*S^2 by linarith)
    (show 0 ≤ 1/25+(6/25)*S by linarith)
  have he : (1-(19/25)*S)*(1+C)+S*C-(24/25)*C*(1+C) =
      1/25+C/25+(24/25)*S^2-(19/25)*S+(6/25)*C*S := by
    linear_combination -(24/25)*hu
  rw [he]
  by_cases hs : S ≤ 1/2
  · have hcubic := mul_nonneg (sq_nonneg S) (show 0 ≤ 1/2-S by linarith)
    have hquad := sq_nonneg (216*S-65)
    nlinarith
  · have hcubic := mul_nonneg (sq_nonneg S) (show 0 ≤ 1-S by linarith)
    have hquad := sq_nonneg (S-1/2)
    nlinarith

/-- A denominator-free support margin, retaining either sign of the second frame. -/
private theorem support_kernel (c s C S : ℝ)
    (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hC : 0 < C) (hSC : |S| ≤ C) (hu : C^2+S^2=1) :
    2*C*(c+(24/25)*s) ≤
      (c*C+s*S)*(C+|S|)+s+C*(c*C+s*S+|c*S-s*C|)-(38/25)*s*S := by
  obtain ⟨hC7,hC1,hS1,hCb⟩ := canonical_bounds C S hC hSC hu
  let P := ((c*C+s*S)*(C+|S|)+s+C*(c*C+s*S+|c*S-s*C|)
    -(38/25)*s*S)/2-C*(c+(24/25)*s)
  suffices hp : 0 ≤ P by dsimp [P] at hp; linarith
  by_cases hS0 : 0 ≤ S
  · have hSC' : S ≤ C := (abs_le.mp hSC).2
    let F := (1-(19/25)*S)*(1+C)+S*C-(24/25)*C*(1+C)
    have hF : 0 < F := positive_slope_margin C S hC hS0 hSC' hu
    have hsF := mul_nonneg hs hF.le
    by_cases hT : 0 ≤ c*S-s*C
    · have ht := mul_nonneg (mul_nonneg hC.le
        (show 0 ≤ 1+C-S by linarith)) hT
      have hid : (1+C)*P = s*F+C*(1+C-S)*(c*S-s*C) := by
        dsimp [P,F]
        rw [abs_of_nonneg hS0, abs_of_nonneg hT]
        linear_combination (c*C+s*(1+C)/2)*hu
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (1+C)*P) (by linarith)
    · have ht := mul_nonneg (mul_nonneg hS0 hC.le)
        (show 0 ≤ -(c*S-s*C) by linarith)
      have hid : (1+C)*P = s*F-S*C*(c*S-s*C) := by
        dsimp [P,F]
        rw [abs_of_nonneg hS0, abs_of_nonpos (le_of_not_ge hT)]
        linear_combination (c*C+s*(1+C)/2)*hu
      exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (1+C)*P) (by linarith)
  · have hS0' : S ≤ 0 := le_of_not_ge hS0
    have ht0 : 0 ≤ -S := neg_nonneg.mpr hS0'
    have htC : -S ≤ C := by simpa [abs_of_nonpos hS0'] using hSC
    have hsum : 1 ≤ C-S := by nlinarith [mul_nonneg hC.le ht0]
    have htwice : 2*C*(-S) ≤ 1 := by nlinarith [sq_nonneg (C+S)]
    have hT : c*S-s*C ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hS0', mul_nonneg hs hC.le]
    have hfirst := mul_nonneg
      (mul_nonneg (mul_nonneg (show 0 ≤ c-s by linarith) hC.le)
        (show 0 ≤ C-S-1 by linarith)) (show 0 ≤ 1+C by linarith)
    have hsecond := mul_nonneg (mul_nonneg hs ht0)
      (show 0 ≤ (19/25)*(1+C)-2*C*(-S) by linarith)
    have hid : (1+C)*(P-C*s/25) =
        (c-s)*C*(C-S-1)*(1+C)+s*(-S)*((19/25)*(1+C)-2*C*(-S)) := by
      dsimp [P]
      rw [abs_of_nonpos hS0', abs_of_nonpos hT]
      linear_combination (s*(3*C-1)/2)*hu
    have hCs := mul_nonneg hC.le hs
    have hp : 0 ≤ P-C*s/25 := nonneg_of_mul_nonneg_right
      (by linarith : 0 ≤ (1+C)*(P-C*s/25)) (by linarith)
    exact (div_nonneg hCs (by norm_num : (0:ℝ) ≤ 25)).trans (sub_nonneg.mp hp)

/-- Original-wall scalar support bound, uniform over the signed L orientation. -/
theorem left_support (a c s C S X Y : ℝ)
    (ha : 1 < a) (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hC : 0 < C) (hSC : |S| ≤ C) (hu : C^2+S^2=1)
    (hwall : a*(C+|S|)/2 ≤ X)
    (hlow : -S*(19/25)+C*(187/100) ≤ -S*X+C*Y-a/2) :
    c+(283/100)*s ≤ c*X+s*Y+a/2*(c*C+s*S+|c*S-s*C|) := by
  have hCS : 0 ≤ C+S := by linarith [(abs_le.mp hSC).1]
  have hD : 0 ≤ c*C+s*S := by
    nlinarith [mul_nonneg (show 0 ≤ c-s by linarith) hC.le, mul_nonneg hs hCS]
  have hDsum : 0 ≤ c*C+s*S+|c*S-s*C| := by linarith [abs_nonneg (c*S-s*C)]
  have hB : 0 ≤ (c*C+s*S)*(C+|S|)+s+C*(c*C+s*S+|c*S-s*C|) := by
    nlinarith [mul_nonneg hD (show 0 ≤ C+|S| by linarith [abs_nonneg S]), mul_nonneg hC.le hDsum]
  have hw := mul_nonneg hD (show 0 ≤ X-a*(C+|S|)/2 by linarith)
  have hv := mul_nonneg hs
    (show 0 ≤ -S*X+C*Y-a/2+S*(19/25)-C*(187/100) by linarith)
  have haB := mul_nonneg (show 0 ≤ a-1 by linarith) hB
  have hk := support_kernel c s C S hc hs hsc hC hSC hu
  have hp : 0 ≤ C*(c*X+s*Y+a/2*(c*C+s*S+|c*S-s*C|)-(c+(283/100)*s)) := by
    nlinarith only [hw,hv,haB,hk]
  have hgap := nonneg_of_mul_nonneg_right hp hC
  linarith

/-- The B-longitudinal separation contradicts the wall-height inequality. -/
theorem b_axis_impossible (a c s C S X Y : ℝ)
    (ha : 1 < a) (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hC : 0 < C) (hSC : |S| ≤ C)
    (hunit : c^2+s^2=1) (hLunit : C^2+S^2=1)
    (hwall : a*(C+|S|)/2 ≤ X)
    (hlow : -S*(19/25)+C*(187/100) ≤ -S*X+C*Y-a/2)
    (hheight : a ≤ s+(293/500)*c)
    (haxis : c*X+s*Y+a/2*(c*C+s*S+|c*S-s*C|)+a ≤
      2*c+(1543/500)*s) : False := by
  have hsupport := left_support a c s C S X Y ha hc hs hsc hC hSC hLunit hwall hlow
  have hlinear : 10 < (4379/500)*c+(599/125)*s := by linarith
  have hnorm := sq_nonneg ((599/125)*c-(4379/500)*s)
  nlinarith only [hnorm,hunit,hlinear,sq_nonneg ((4379/500)*c+(599/125)*s-10)]

/-- Exact quartic margin used for the smaller positive L angle. -/
theorem smaller_angle_margin (C S : ℝ) (hC : 0 < C)
    (hS0 : 0 ≤ S) (hSC : S ≤ C) (hu : C^2+S^2=1) :
    0 < C*(1-(1157/1000)*S)+S+(129/1000)*S^2-889/1000 := by
  have hs71 : S ≤ 71/100 := by nlinarith [mul_nonneg (sub_nonneg.mpr hSC) (add_nonneg hC.le hS0)]
  let z := S-3/5
  have hz0 : -3/5 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 11/100 := by dsimp [z]; linarith
  have hbox := mul_nonneg (show 0 ≤ z+3/5 by linarith)
    (show 0 ≤ 11/100-z by linarith)
  have hbracket : 19/100 < 1706923/5000000-(149587/125000)*z-(135529/100000)*z^2 := by
    nlinarith
  have hpositive := mul_nonneg (sq_nonneg z) (le_of_lt (sub_pos.mpr hbracket))
  have hquad := sq_nonneg ((38/100)*z-60967/12500000)
  have hp : 0 < 209679/1000000-(67/125)*S-(431989/1000000)*S^2+
      (257/125)*S^3-(135529/100000)*S^4 := by
    dsimp [z] at hpositive hquad
    nlinarith
  have hfactor : 0 ≤ 1-(1157/1000)*S := by linarith
  have hleft := mul_nonneg hC.le hfactor
  have heq := congrArg (fun t : ℝ => t*(1-(1157/1000)*S)^2) hu
  by_contra h
  have hbad : 0 ≤ (889/1000-S-(129/1000)*S^2)-C*(1-(1157/1000)*S) := by linarith
  have hsum : 0 ≤ (889/1000-S-(129/1000)*S^2)+C*(1-(1157/1000)*S) := by linarith
  nlinarith [mul_nonneg hbad hsum]


private theorem shape_coefficients (c s : ℝ) (hc : 0 < c)
    (hs : 0 ≤ s) (hsc : s ≤ c) (hu : c^2+s^2=1)
    (hw : 34/25 < c+s) :
    -889/1000 < c+s-2-(293/500)*c*s ∧
    c-s+(293/500)*s^2 < 527/1000 ∧ 12/25 < s := by
  have hw2 := mul_pos (sub_pos.mpr hw) (show 0 < c+s+34/25 by linarith)
  have hd : c-s < 97/250 := by nlinarith [sq_nonneg (c-s-97/250)]
  have hwtop : c+s ≤ 283/200 := by nlinarith [sq_nonneg (c-s)]
  have hprod := mul_nonneg (show 0 ≤ c+s-34/25 by linarith)
    (show 0 ≤ 1-(293/1000)*(c+s+34/25) by linarith)
  have hdw := mul_nonneg (show 0 ≤ c-s by linarith)
    (show 0 ≤ c+s-34/25 by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · linarith

/-- Exact margin for the larger positive L angle. -/
theorem larger_angle_margin (C S : ℝ) (hC : 0 < C)
    (hS0 : 0 ≤ S) (hSC : S ≤ C) (hu : C^2+S^2=1)
    (hs48 : 12/25 ≤ S) :
    0 < 2*C-2+S-(152/125)*C*S+(31/25)*S^2 := by
  obtain ⟨hC7,hC1,hS1,hCb⟩ :=
    canonical_bounds C S hC (by simpa [abs_of_nonneg hS0] using hSC) hu
  rw [abs_of_nonneg hS0] at hS1
  have hSpos : 0 < S := by linarith
  by_cases hs : S ≤ 3/5
  · have hSsq := mul_nonneg hS0 (show 0 ≤ 3/5-S by linarith)
    have hC8 : 4/5 ≤ C := by nlinarith
    have hb := mul_nonneg (show 0 ≤ 1-C by linarith)
      (show 0 ≤ (5/9)*C-4/9 by linarith)
    have hcub := mul_nonneg (show 0 ≤ C-1+(5/9)*S^2 by nlinarith)
      (show 0 ≤ 2-(152/125)*S by linarith)
    have hssq := mul_nonneg (show 0 ≤ S-12/25 by linarith)
      (show 0 ≤ S+12/25 by linarith)
    have hq : 0 < -27/125+(29/225)*S+(152/225)*S^2 := by nlinarith
    have hp := mul_pos hSpos hq
    nlinarith
  · have hcub := mul_nonneg (show 0 ≤ C-1+(3/5)*S^2 by linarith)
      (show 0 ≤ 2-(152/125)*S by linarith)
    have hssq := mul_nonneg (show 0 ≤ S-3/5 by linarith)
      (show 0 ≤ S+3/5 by linarith)
    have hq : 0 < -27/125+S/25+(456/625)*S^2 := by nlinarith
    have hp := mul_pos hSpos hq
    nlinarith

/-- The L-longitudinal separation is impossible in all three signed
relative-angle cases. Each input is an ordinary scalar wall/support bound. -/
theorem l_axis_impossible (a c s C S U : ℝ)
    (ha : 1 < a) (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hC : 0 < C) (hSC : |S| ≤ C)
    (hunit : c^2+s^2=1) (hLunit : C^2+S^2=1)
    (hw : 34/25 < c+s)
    (hwallPos : 0 ≤ S → a*(1+S/C)+(187/100)*S-(19/25)*S^2/C ≤ U)
    (hwallNeg : S ≤ 0 → a-(457/500)*S^2/C+2*S ≤ U)
    (hcapPos : 0 ≤ c*S-s*C → U ≤ C*(1+c^2)+S*(1543/500+c*s)-a*(c*C+s*S+c*S-s*C))
    (hcapNeg : c*S-s*C ≤ 0 → U ≤ C*(2+(293/500)*c*s)+S*(5/2+(293/500)*s^2)-a*(c*C+s*S-(c*S-s*C))) :
    False := by
  obtain ⟨hC7,hC1,hS1,hCb⟩ := canonical_bounds C S hC hSC hLunit
  obtain ⟨hc7,hc1,hs1,hcb⟩ := canonical_bounds c s hc
    (by simpa [abs_of_nonneg hs] using hsc) hunit
  obtain ⟨hcoef1,hcoef2,hs48⟩ := shape_coefficients c s hc hs hsc hunit hw
  have hD : 0 ≤ c*C+s*S := by
    have hCS : 0 ≤ C+S := by linarith [(abs_le.mp hSC).1]
    nlinarith [mul_nonneg (show 0 ≤ c-s by linarith) hC.le, mul_nonneg hs hCS]
  have hdiv1 : C*(S/C)=S := by field_simp [ne_of_gt hC]
  have hdiv19 : C*((19/25)*S^2/C)=(19/25)*S^2 := by field_simp [ne_of_gt hC]; ring
  have hdiv457 : C*((457/500)*S^2/C)=(457/500)*S^2 := by field_simp [ne_of_gt hC]; ring
  have ha0 : 0 ≤ a-1 := by linarith
  by_cases hT : 0 ≤ c*S-s*C
  · have hSpos : 0 < S := by nlinarith only [hT,hc,mul_pos (show 0 < s by linarith only [hs48]) hC]
    have hSC' : S ≤ C := (abs_le.mp hSC).2
    have hSs : s ≤ S := by
      apply le_of_not_gt
      intro hlt
      have hcc : c < C := by nlinarith only [hunit,hLunit,hc,hC,mul_pos (sub_pos.mpr hlt) (show 0 < s+S by linarith only [hs,hSpos])]
      have hfirst := mul_neg_of_pos_of_neg hc (sub_neg.mpr hlt)
      have hsecond := mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hcc.le)
      nlinarith only [hfirst,hsecond,hT]
    have hCc : C ≤ c := by nlinarith only [hunit,hLunit,hc,hC,mul_nonneg (sub_nonneg.mpr hSs) (show 0 ≤ S+s by linarith only [hs,hSpos])]
    have hQ : 0 ≤ c*C-s*S := by
      nlinarith only [mul_nonneg (show 0 ≤ c-s by linarith only [hsc]) hC.le,
        mul_nonneg hs (sub_nonneg.mpr hSC')]
    have hcross := mul_nonneg hT hQ
    have hcrossid : (c*S-s*C)*(c*C-s*S)=C*S-c*s := by
      linear_combination C*S*hunit-c*s*hLunit
    have hww : c+s ≤ C+S := by
      apply le_of_not_gt
      intro hlt
      have hh := mul_pos (sub_pos.mpr hlt)
        (show 0 < c+s+(C+S) by linarith only [hc,hs,hC,hSpos])
      nlinarith only [hh,hcross,hcrossid,hunit,hLunit]
    have hAprod := mul_nonneg (sub_nonneg.mpr hCc)
      (show 0 ≤ 2-c-C by linarith)
    have hA : C-S-1-C^2 ≤ c-s-1-c^2 := by nlinarith only [hAprod,hww]
    have hBprod := mul_nonneg (show 0 ≤ C+S-(c+s) by linarith)
      (show 0 ≤ C+S+c+s-2 by linarith)
    have hB : C+S-152/125-C*S ≤ c+s-152/125-c*s := by nlinarith only [hBprod,hunit,hLunit]
    have hweightA := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hA)
    have hweightB := mul_nonneg (mul_nonneg hSpos.le hC.le) (sub_nonneg.mpr hB)
    have hmargin := larger_angle_margin C S hC hSpos.le hSC' hLunit (by linarith)
    have hid : C+S+C^2*(C-S-1-C^2)+S*C*(C+S-152/125-C*S)-(19/25)*S^2 =
        2*C-2+S-(152/125)*C*S+(31/25)*S^2 := by
      linear_combination (C-C^2-2)*hLunit
    have hfactor : 0 ≤ 1+S/C+(c*C+s*S)+(c*S-s*C) := by
      linarith [div_nonneg hSpos.le hC.le]
    have haF := mul_nonneg ha0 hfactor
    have hspan : 1+S/C+(c*C+s*S)+(c*S-s*C) ≤
        C*(1+c^2)+S*(152/125+c*s)+(19/25)*S^2/C := by
      nlinarith only [haF,hwallPos hSpos.le,hcapPos hT]
    have hm := mul_le_mul_of_nonneg_left hspan hC.le
    simp only [mul_add,mul_sub,mul_one,hdiv1,hdiv19] at hm
    nlinarith only [hm,hweightA,hweightB,hmargin,hid]
  · have hT' : c*S-s*C ≤ 0 := le_of_not_ge hT
    by_cases hSneg : S ≤ 0
    · have hfactor : 0 ≤ 1+(c*C+s*S)-(c*S-s*C) := by linarith
      have haF := mul_nonneg ha0 hfactor
      have hspan : 1+(c*C+s*S)-(c*S-s*C) ≤
          C*(2+(293/500)*c*s)+S*(1/2+(293/500)*s^2)+(457/500)*S^2/C := by
        nlinarith only [haF,hwallNeg hSneg,hcapNeg hT']
      have hm := mul_le_mul_of_nonneg_left hspan hC.le
      have hcs : c*s ≤ 1/2 := by nlinarith only [hunit,sq_nonneg (c-s)]
      have hcoarse := mul_nonneg (sq_nonneg C)
        (show 0 ≤ c+s-2-(293/500)*c*s+943/1000 by linarith)
      have hrest := mul_nonneg (mul_nonneg (neg_nonneg.mpr hSneg) hC.le)
        (show 0 ≤ c-s+(293/500)*s^2 by nlinarith only [hsc,sq_nonneg s])
      have hCS : 0 ≤ C+S := by linarith [(abs_le.mp hSC).1]
      have hdiff := mul_nonneg hCS (show 0 ≤ C-S by linarith)
      have ht := mul_nonneg (neg_nonneg.mpr hSneg) hCS
      have hmargin : 0 < C-(943/1000)*C^2-S*C/2-(457/500)*S^2 := by
        nlinarith only [hCb,hLunit,hdiff,ht,mul_pos hC hC]
      simp only [mul_add,mul_sub,mul_one,hdiv457] at hm
      nlinarith only [hm,hcoarse,hrest,hmargin]
    · have hSpos : 0 ≤ S := le_of_not_ge hSneg
      have hSC' : S ≤ C := (abs_le.mp hSC).2
      have hfactor : 0 ≤ 1+S/C+(c*C+s*S)-(c*S-s*C) := by
        linarith [div_nonneg hSpos hC.le]
      have haF := mul_nonneg ha0 hfactor
      have hspan : 1+S/C+(c*C+s*S)-(c*S-s*C) ≤
          C*(2+(293/500)*c*s)+S*(63/100+(293/500)*s^2)+(19/25)*S^2/C := by
        nlinarith only [haF,hwallPos hSpos,hcapNeg hT']
      have hm := mul_le_mul_of_nonneg_left hspan hC.le
      have hc1 := mul_nonneg (sq_nonneg C) (show 0 ≤ c+s-2-(293/500)*c*s+889/1000 by linarith)
      have hc2 := mul_nonneg (mul_nonneg hSpos hC.le)
        (show 0 ≤ 527/1000-(c-s+(293/500)*s^2) by linarith)
      have hmargin := smaller_angle_margin C S hC hSpos hSC' hLunit
      simp only [mul_add,mul_sub,mul_one,hdiv1,hdiv19] at hm
      nlinarith only [hm,hc1,hc2,hmargin,hLunit]

end N12Compact.FourSquareLongitudinal
