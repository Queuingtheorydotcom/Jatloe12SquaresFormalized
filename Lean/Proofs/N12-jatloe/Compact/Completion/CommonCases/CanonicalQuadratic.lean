import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.Ring

/-! Rational endpoint comparisons on the unit circle without square roots.
A factored quadratic difference bounds a linear projection on either side
of a rational slope. The closed slope equality is included in both lemmas. -/
namespace N12Compact.CommonCases.CanonicalQuadratic
set_option Elab.async false

def firstCoeff (a b n m : ℝ) : ℝ := 2*n*a*b+m*(b^2-a^2)
def secondCoeff (a b n m : ℝ) : ℝ := n*(b^2-a^2)-2*m*a*b

private theorem factor_identity (c s a b n m : ℝ) (unit : c^2+s^2=1) :
    (n*a+m*b)^2-(n^2+m^2)*(a*c+b*s)^2=
      (m*c-n*s)*(firstCoeff a b n m*c+secondCoeff a b n m*s) := by
  unfold firstCoeff secondCoeff
  linear_combination -(n*a+m*b)^2*unit

private theorem strict_projection (L N K : ℝ) (np : 0<N) (margin : K<N)
    (bound : N*L^2≤K) : L<1 := by
  apply lt_of_not_ge
  intro large
  have square : 1≤L^2 := by nlinarith only [large,sq_nonneg (L-1)]
  have weighted := mul_nonneg np.le (sub_nonneg.mpr square)
  nlinarith only [weighted,bound,margin]

theorem before_one (c s a b n m : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (normal : 0<n^2+m^2)
    (margin : (n*a+m*b)^2<n^2+m^2) (cut : n*s≤m*c)
    (first : 0≤firstCoeff a b n m) (second : 0≤secondCoeff a b n m) :
    a*c+b*s<1 := by
  have weight := add_nonneg (mul_nonneg first cn) (mul_nonneg second sn)
  have product := mul_nonneg (sub_nonneg.mpr cut) weight
  have identity := factor_identity c s a b n m unit
  exact strict_projection (a*c+b*s) (n^2+m^2) ((n*a+m*b)^2)
    normal margin (by linarith only [identity,product])

theorem after_one (c s a b n m : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (normal : 0<n^2+m^2)
    (margin : (n*a+m*b)^2<n^2+m^2) (cut : m*c≤n*s)
    (first : firstCoeff a b n m≤0) (second : secondCoeff a b n m≤0) :
    a*c+b*s<1 := by
  have weight := add_nonneg (mul_nonneg (neg_nonneg.mpr first) cn)
    (mul_nonneg (neg_nonneg.mpr second) sn)
  have product := mul_nonneg (sub_nonneg.mpr cut) weight
  have identity : (n*a+m*b)^2-(n^2+m^2)*(a*c+b*s)^2=
      (n*s-m*c)*((-firstCoeff a b n m)*c+(-secondCoeff a b n m)*s) := by
    calc
      _ = (m*c-n*s)*(firstCoeff a b n m*c+secondCoeff a b n m*s) :=
        factor_identity c s a b n m unit
      _ = _ := by ring
  exact strict_projection (a*c+b*s) (n^2+m^2) ((n*a+m*b)^2)
    normal margin (by linarith only [identity,product])

end N12Compact.CommonCases.CanonicalQuadratic
