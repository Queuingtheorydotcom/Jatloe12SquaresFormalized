import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Exact scalar comparisons for the negative corner coupling. These
are continuous unit-normal inequalities, with no saved pose enclosures. -/
namespace N12Compact.C977CornerCubic

def Normal (c t : ℝ) : Prop := 0 ≤ t ∧ t ≤ c ∧ c^2+t^2=1

theorem normal_bounds {c t : ℝ} (h : Normal c t) :
    (7/10 : ℝ) ≤ c ∧ c ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
      1 ≤ c+t ∧ c+t ≤ 10/7 := by
  obtain ⟨ht, htc, hn⟩ := h
  have hc : 0 ≤ c := le_trans ht htc
  have hdiff := mul_nonneg (sub_nonneg.mpr htc) (add_nonneg hc ht)
  have hc7 : (7/10 : ℝ) ≤ c := by
    by_contra no
    have hm := mul_nonneg hc (show 0 ≤ 7/10-c by linarith only [no])
    nlinarith only [hn, hdiff, no, hm]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg t, sq_nonneg (c-1)]
  have ht1 : t ≤ 1 := le_trans htc hc1
  have hprod := mul_nonneg hc ht
  have sumlo : 1 ≤ c+t := by
    by_contra no
    have hm := mul_nonneg (add_nonneg hc ht)
      (show 0 ≤ 1-(c+t) by linarith only [no])
    nlinarith only [hn, hprod, no, hm]
  have sumhi : c+t ≤ 10/7 := by
    nlinarith [sq_nonneg (c-t), sq_nonneg (c+t-10/7)]
  exact ⟨hc7, hc1, ht, ht1, sumlo, sumhi⟩

noncomputable def boundary (c t : ℝ) : ℝ := 1+t+t*(1-t)/c

def H (f g r : ℝ) : ℝ := (2-g)+(1-2*f)*r+g*r^2-r^3

/-- Exact chord decomposition for the cubic. No derivative or convexity
oracle is needed; the correction is an explicit nonnegative product. -/
theorem cubic_chord (f g rho r : ℝ)
    (hrho : rho < 1) (hr0 : rho ≤ r) (hr1 : r ≤ 1)
    (he0 : 0 ≤ H f g rho) (he1 : 0 ≤ H f g 1)
    (hfactor : 0 ≤ r+1+rho-g) : 0 ≤ H f g r := by
  have first := mul_nonneg (sub_nonneg.mpr hr1) he0
  have second := mul_nonneg (sub_nonneg.mpr hr0) he1
  have correction := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hr0) (sub_nonneg.mpr hr1)) hfactor
  have scaled := mul_nonneg (show 0 ≤ 1-rho by linarith only [hrho]) correction
  have identity : (1-rho)*H f g r =
      (1-r)*H f g rho+(r-rho)*H f g 1+
        (1-rho)*(r-rho)*(1-r)*(r+1+rho-g) := by
    unfold H; ring
  have nonneg : 0 ≤ (1-rho)*H f g r := by
    nlinarith only [identity, first, second, scaled]
  exact nonneg_of_mul_nonneg_right nonneg (by linarith only [hrho])

/-- The delicate coefficient bound has a rational sum-of-squares
certificate with a positive constant remainder. -/
theorem wing_coefficient {C T : ℝ} (h : Normal C T) :
    1+T^2+(22/25)*C*T+C-T ≤ 2 := by
  have bounds := normal_bounds h
  obtain ⟨hT, hTC, hn⟩ := h
  have hC : 0 ≤ C := by linarith only [bounds.1]
  have hCm : 0 ≤ 1-C := by linarith only [bounds.2.1]
  have hcoef : 0 ≤ 1-(22/25)*C := by linarith only [bounds.2.1]
  have left_nonneg := mul_nonneg hT hcoef
  have right_nonneg := mul_nonneg hC hCm
  have cert : 0 ≤ 625-475*C-1241*C^2+1109*C^3 := by
    have term0 := mul_nonneg (show 0 ≤ C-7/10 by linarith only [bounds.1])
      (sq_nonneg (C-9/10))
    have term1 := sq_nonneg (C-9/10)
    have term2 := sq_nonneg (100*(C-9/10)-1)
    have identity : 625-475*C-1241*C^2+1109*C^3 =
        1109*(C-7/10)*(C-9/10)^2+835*(C-9/10)^2+
          (1393/20000)*(100*(C-9/10)-1)^2+13627/20000 := by ring
    nlinarith only [identity, term0, term1, term2]
  have product := mul_nonneg hCm cert
  have identity :
      625*((T*(1-(22/25)*C))^2-(C*(1-C))^2) =
        (1-C)*(625-475*C-1241*C^2+1109*C^3) := by
    have hT2 : T^2=1-C^2 := by linarith only [hn]
    calc
      _ = 625*(T^2*(1-(22/25)*C)^2-C^2*(1-C)^2) := by ring
      _ = _ := by rw [hT2]; ring
  have compare : C*(1-C) ≤ T*(1-(22/25)*C) := by
    by_contra no
    have difference : T*(1-(22/25)*C)-C*(1-C) < 0 := by linarith only [no]
    have sum : 0 < T*(1-(22/25)*C)+C*(1-C) := by
      linarith only [no, left_nonneg]
    have bad := mul_neg_of_neg_of_pos difference sum
    nlinarith only [identity, product, bad]
  nlinarith only [compare, hn]

theorem low_coefficient {C T : ℝ} (h : Normal C T) :
    2-(22/25)*T^2+C*T-C-T ≤ 1 := by
  have b := normal_bounds h
  have hn := h.2.2
  have hC23 : (2/3 : ℝ) ≤ C := by linarith only [b.1]
  have hdef : 1-C ≤ (3/5)*T^2 := by
    have product := mul_nonneg (show 0 ≤ C-2/3 by linarith only [hC23])
      (show 0 ≤ 1-C by linarith only [b.2.1])
    nlinarith only [product, hn]
  have product := mul_nonneg (sq_nonneg T) h.1
  have multiply := mul_nonneg (show 0 ≤ (3/5)*T^2-(1-C) by linarith only [hdef])
    (show 0 ≤ 1-T by linarith only [b.2.2.2.1])
  nlinarith only [multiply, product, hn, sq_nonneg T]

theorem high_tilt_coefficient {C T : ℝ} (h : Normal C T)
    (high : (3/5 : ℝ) ≤ T) :
    2-(22/25)*T^2+C*T-C-T ≤ 4/5 := by
  have b := normal_bounds h
  have hn := h.2.2
  have hdef : 1-C ≤ (3/5)*T^2 := by
    have product := mul_nonneg (show 0 ≤ C-2/3 by linarith only [b.1])
      (show 0 ≤ 1-C by linarith only [b.2.1])
    nlinarith only [product, hn]
  have multiply := mul_nonneg (show 0 ≤ (3/5)*T^2-(1-C) by linarith only [hdef])
    (show 0 ≤ 1-T by linarith only [b.2.2.2.1])
  have high2 : (9/25 : ℝ) ≤ T^2 := by nlinarith only [high, h.1]
  have cubic := mul_nonneg (sq_nonneg T)
    (show 0 ≤ T-3/5 by linarith only [high])
  nlinarith only [multiply, cubic, high2, hn]

end N12Compact.C977CornerCubic
