import Compact.Geometry.C977CornerSectorBounds

/-! Continuous margins for a positive bottom singleton and a negative
central square. The new C696 central crosspoint removes the longitudinal
axis with a fixed positive margin. The remaining transverse comparison
uses the exact short coefficient vector (7/20,457/500). -/
namespace N12Compact.C696CornerMargins

open C977CornerCubic C977CornerSectorBounds

noncomputable def boundary (c s : ℝ) : ℝ :=
  1+s/c-2*s-(457/500)*s^2/c

private theorem sum_margin {c s : ℝ} (h : Normal c s) :
    (4/5)*c*s ≤ c+s-1 := by
  have b := normal_bounds h
  have product := mul_nonneg
    (show 0≤c+s-1 by linarith only [b.2.2.2.2.1])
    (show 0≤3/2-(c+s) by linarith only [b.2.2.2.2.2])
  nlinarith only [product,h.2.2]

/-- A positive fixed margin excludes the corner square's longitudinal
axis. The coefficient 3/2 comes from the actual new C696 point (3/2,2). -/
theorem longitudinal {c s C T : ℝ} (h : Normal c s) (H : Normal C T) :
    c*(3/2+(1/2)*T^2-T)+s*(2+(1/2)*C*T-C) <
      (187/100)*c+(19/25)*s := by
  have b := normal_bounds h
  have B := normal_bounds H
  have hc : 0<c := by linarith only [b.1]
  have orderSquare := mul_nonneg H.1 (sub_nonneg.mpr H.2.1)
  have squareOrder := mul_nonneg (sub_nonneg.mpr H.2.1)
    (show 0≤C+T by linarith only [B.1,H.1])
  have half : T^2≤1/2 := by nlinarith only [squareOrder,H.2.2]
  have sum := sum_margin H
  have margin : 9/10≤(C+T)*(1-T/2) := by
    nlinarith only [sum,orderSquare,half]
  have ct := mul_nonneg (show 0≤C by linarith only [B.1]) H.1
  have negative : C-31/25-C*T/2≤0 := by nlinarith only [B.2.1,ct]
  have replacement := mul_nonneg (sub_nonneg.mpr h.2.1) (neg_nonneg.mpr negative)
  have scaled := mul_pos hc (show 0<(3/100:ℝ) by norm_num)
  have weighted := mul_nonneg hc.le
    (show 0≤(C+T)*(1-T/2)-9/10 by linarith only [margin])
  nlinarith only [replacement,scaled,weighted]

/-- A support line with these two coefficient bounds lies below the
actual bottom singleton's transverse bound. -/
theorem comparison {c s f g : ℝ} (h : Normal c s)
    (hf : f≤1) (hg : (33/20:ℝ)≤g) :
    c*f-s*g ≤ boundary c s := by
  have b := normal_bounds h
  have hc : 0<c := by linarith only [b.1]
  have short : (7/20)*c+(457/500)*s≤1 := by
    nlinarith only [h.2.2,sq_nonneg (c-7/20),sq_nonneg (s-457/500)]
  have first := mul_nonneg hc.le (sub_nonneg.mpr b.2.1)
  have second := mul_nonneg h.1 (sub_nonneg.mpr short)
  have formula : c*boundary c s=c+s-2*c*s-(457/500)*s^2 := by
    unfold boundary
    field_simp [ne_of_gt hc]
    <;> ring
  have simple : c-(33/20)*s≤boundary c s := by
    have scaled : 0≤c*(boundary c s-(c-(33/20)*s)) := by
      nlinarith only [formula,first,second]
    have gap := nonneg_of_mul_nonneg_right scaled hc
    linarith only [gap]
  have fprod := mul_nonneg hc.le (sub_nonneg.mpr hf)
  have gprod := mul_nonneg h.1 (sub_nonneg.mpr hg)
  nlinarith only [simple,fprod,gprod]

theorem left_comparison {c s C T : ℝ} (h : Normal c s) (H : Normal C T) :
    c*(2+(T-1)/C-T)-s*(1+C) ≤ boundary c s := by
  have b := normal_bounds H
  have hC : 0<C := by linarith only [b.1]
  apply comparison h
  · have prod := mul_nonneg (sub_nonneg.mpr b.2.1)
      (sub_nonneg.mpr b.2.2.2.1)
    have frac : C*((T-1)/C)=T-1 := by field_simp [ne_of_gt hC]
    have scaled : 0≤C*(1-(2+(T-1)/C-T)) := by nlinarith only [prod,frac]
    have gap := nonneg_of_mul_nonneg_right scaled hC
    linarith only [gap]
  · linarith only [b.1]

theorem near_comparison {c s C T : ℝ} (h : Normal c s) (H : Normal C T) :
    c*(2-(22/25)*T^2+C*T-C-T)-
      s*(1+T^2+(22/25)*C*T+C-T) ≤ boundary c s := by
  have b := normal_bounds H
  apply comparison h (low_coefficient H)
  have prod := mul_nonneg H.1 (show 0≤C-7/10 by linarith only [b.1])
  nlinarith only [prod,b.1,sq_nonneg (T-24/125)]

/-- The central transverse axis cannot separate above this corner
square if the central upper face misses (2,2). -/
theorem central_axis {c s C T : ℝ} (h : Normal c s) (H : Normal C T)
    (tilt : 0<s) :
    2*(C+T) ≤ (T/s)*(1-c+s)+(c*T+s*C)+(c*C-s*T)+1 := by
  have b := normal_bounds h
  have B := normal_bounds H
  have cs := mul_nonneg h.1 (sub_nonneg.mpr h.2.1)
  have norm : (2-c-s)^2+s^2≤1 := by
    have sum := sum_margin h
    nlinarith only [h.2.2,sum,cs,sq_nonneg s]
  have dot : (2-c-s)*C+s*T≤1 := by
    nlinarith only [norm,H.2.2,sq_nonneg (2-c-s-C),sq_nonneg (s-T)]
  have product := mul_nonneg
    (mul_nonneg H.1 (sub_nonneg.mpr b.2.1))
    (sub_nonneg.mpr b.2.2.2.1)
  have quotient := div_nonneg product tilt.le
  have identity :
      (T/s)*(1-c+s)+(c*T+s*C)+(c*C-s*T)+1-2*(C+T)=
        1-((2-c-s)*C+s*T)+T*(1-c)*(1-s)/s := by
    field_simp [ne_of_gt tilt]
    <;> ring
  linarith only [identity,dot,quotient]

end N12Compact.C696CornerMargins
