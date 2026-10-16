import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.Ring

/-! Exact projection margins used in Theorem 1 of
ORDINARY-LEFT-TOP-OBSTRUCTION.md.  The rational endpoint comparison below
replaces its square-root and monotonicity calculations.  This file is a
source translation; it does not assert that a Lean replay has been run. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins
set_option Elab.async false

private theorem lt_one_of_square (z : ℝ) (bound : z^2 < 1) : z < 1 := by
  by_contra failure
  have lower : 1 ≤ z := le_of_not_gt failure
  have product := mul_nonneg (sub_nonneg.mpr lower)
    (show 0 ≤ z+1 by linarith only [lower])
  nlinarith only [bound,product]

/-- A rational tangent-direction bound for a unit vector.  The comparison
is linear in `c,s`; the remaining strict margin is an exact rational square.
No positivity assumption on the compared expression is necessary. -/
private theorem endpoint (c s m n k z : ℝ) (unit : c^2+s^2=1)
    (comparison : z ≤ k*(m*c+n*s))
    (margin : k^2*(m^2+n^2) < 1) : z < 1 := by
  have identity : (m*c+n*s)^2+(n*c-m*s)^2 = m^2+n^2 := by
    calc
      _ = (m^2+n^2)*(c^2+s^2) := by ring
      _ = m^2+n^2 := by rw [unit]; ring
  have norm : (m*c+n*s)^2 ≤ m^2+n^2 := by
    calc
      _ ≤ (m*c+n*s)^2+(n*c-m*s)^2 :=
        le_add_of_nonneg_right (sq_nonneg (n*c-m*s))
      _ = m^2+n^2 := identity
  have square : (k*(m*c+n*s))^2 < 1 := by
    calc
      _ = k^2*(m*c+n*s)^2 := by ring
      _ ≤ k^2*(m^2+n^2) := mul_le_mul_of_nonneg_left norm (sq_nonneg k)
      _ < 1 := margin
  exact lt_of_le_of_lt comparison (lt_one_of_square _ square)

theorem threeTenths (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) : (3/10)*c+s < 1 := by
  apply endpoint c s 1 1 (13/20) ((3/10)*c+s) unit
  · linarith only [order]
  · norm_num

theorem sixHundredths (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) : (3/50)*c+s < 1 := by
  apply endpoint c s 1 1 (53/100) ((3/50)*c+s) unit
  · linarith only [order]
  · norm_num

theorem twentySevenOneOhFour (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) :
    (27/100)*c+(26/25)*s < 1 := by
  apply endpoint c s 1 1 (131/200) ((27/100)*c+(26/25)*s) unit
  · linarith only [order]
  · norm_num

theorem seventeenOneOhFour (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) :
    (17/100)*c+(26/25)*s < 1 := by
  apply endpoint c s 1 1 (121/200) ((17/100)*c+(26/25)*s) unit
  · linarith only [order]
  · norm_num

theorem smallSine (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : (3/7)*c ≤ s) :
    c+(43/500)*s < 1 := by
  apply N12Compact.CommonCases.CanonicalScalars.c_small_sine c s cp sn unit
  linarith only [slope,cp]

theorem halfBeforeTwoThirds (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : s ≤ (2/3)*c) :
    (1/2)*c+s < 1 := by
  apply endpoint c s 3 2 (7/26) ((1/2)*c+s) unit
  · linarith only [slope]
  · norm_num

theorem lowTwoThirds (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : s ≤ (2/3)*c) :
    (263/500)*c+s < 1 := by
  apply endpoint c s 3 2 (1789/6500) ((263/500)*c+s) unit
  · linarith only [slope]
  · norm_num

theorem lowSixth (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : s ≤ c/6) :
    (413/500)*c+s < 1 := by
  apply endpoint c s 6 1 (1489/9250) ((413/500)*c+s) unit
  · linarith only [slope]
  · norm_num

/-- The unit-circle deficit for `c + .06*s`, avoiding half-angle divisions. -/
theorem sixthSlopeSine (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : c/6 < s) :
    c+(3/50)*s < 1 := by
  have sp : 0 < s := by linarith only [slope,cp]
  have coefficient : 0 < (2491/2500)*s-(3/25)*c := by
    linarith only [slope,cp]
  have product := mul_pos sp coefficient
  nlinarith only [unit,product,cp,sn]

theorem oneOhFourSeventeen (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : (2/3)*c ≤ s) :
    (26/25)*c+(17/100)*s < 1 := by
  apply endpoint c s 3 2 (173/650) ((26/25)*c+(17/100)*s) unit
  · linarith only [slope]
  · norm_num

theorem pointUpperV (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : (2/3)*c ≤ s) :
    (26/25)*c-(1/100)*s < 1 := by
  apply endpoint c s 3 2 (31/130) ((26/25)*c-(1/100)*s) unit
  · linarith only [slope]
  · norm_num

theorem highEightElevenths (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : (8/11)*c ≤ s) :
    (26/25)*c+(27/100)*s < 1 := by
  apply endpoint c s 11 8 (68/925) ((26/25)*c+(27/100)*s) unit
  · linarith only [slope]
  · norm_num

theorem pointUpperU (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : s ≤ (8/11)*c) :
    (243/500)*c+s < 1 := by
  apply endpoint c s 11 8 (6673/92500) ((243/500)*c+s) unit
  · linarith only [slope]
  · norm_num

theorem originUpper (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) (slope : s ≤ (8/11)*c) :
    (11/25)*c+s < 1 := by
  apply endpoint c s 11 8 (321/4625) ((11/25)*c+s) unit
  · linarith only [slope]
  · norm_num

end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins
