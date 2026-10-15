import S12.ShortCluster.Projections
import S12.WallGeometry

/-! Exact scalar comparisons from C1092-WALL-SIGN-CHORD, Theorem 1.
The half-angle factorization covers the entire closed orientation interval.
Source translation only; this module has not been compiled. -/
namespace N12Compact.WallSignChord
set_option Elab.async false
noncomputable section

theorem canonical_bounds (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (order : s≤c) (unit : c^2+s^2=1) :
    7/10<c ∧ c≤1 ∧ 1+(4/5)*c*s≤c+s ∧ 1-(3/5)*s^2≤c := by
  have cp : 7/10<c := by
    by_contra no
    have product := mul_nonneg (sub_nonneg.mpr order) (add_nonneg cn sn)
    have small := mul_nonneg (show 0≤7/10-c by linarith only [no])
      (show 0≤7/10+c by linarith only [cn])
    nlinarith only [product,small,unit]
  have c1 : c≤1 := by nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
  have cs := mul_nonneg cn sn
  have sumLow : 1≤c+s := by nlinarith only [unit,cs,cn,sn]
  have sumHigh : c+s≤3/2 := by nlinarith only [unit,sq_nonneg (c-s),cn,sn]
  have strong : 1+(4/5)*c*s≤c+s := by
    nlinarith only [unit,
      mul_nonneg (sub_nonneg.mpr sumHigh) (sub_nonneg.mpr sumLow)]
  have lower : 1-(3/5)*s^2≤c := by
    have product := mul_nonneg (sub_nonneg.mpr c1)
      (show 0≤3*c-2 by linarith only [cp])
    nlinarith only [product,unit]
  exact ⟨cp,c1,strong,lower⟩

/-- The manuscript's completed-square cubic, without an angle subdivision. -/
private theorem gap_nonnegative (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) :
    0≤1+c*(c+s)-2*c-(39/50)*s ∧
      (0<s → 0<1+c*(c+s)-2*c-(39/50)*s) := by
  let z := s/(1+c)
  have den : 0<1+c := by linarith only [cn]
  have zn : 0≤z := div_nonneg sn den.le
  have relation : z*(1+c)=s := div_mul_cancel₀ _ den.ne'
  have half : s*z=1-c := by
    apply (mul_right_cancel₀ den.ne')
    linear_combination s*relation+unit
  have cf : c=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff (by positivity : (1+z^2:ℝ)≠0)).mpr
    linear_combination z*relation+half
  have sf : s=2*z/(1+z^2) := by
    apply (eq_div_iff (by positivity : (1+z^2:ℝ)≠0)).mpr
    linear_combination z*half-relation
  have polynomial : 0<100*z^3-89*z^2+11 := by
    have nonnegative := mul_nonneg (sq_nonneg (z-89/150))
      (show 0≤z+89/300 by linarith only [zn])
    nlinarith only [nonnegative]
  have identity :
      (1+c*(c+s)-2*c-(39/50)*s)*(25*(1+z^2)^2)=
        z*(100*z^3-89*z^2+11) := by
    rw [cf,sf]
    field_simp
    <;> ring
  have denominator : 0<25*(1+z^2)^2 := by positivity
  constructor
  · have product := mul_nonneg zn polynomial.le
    have scaled : 0≤(1+c*(c+s)-2*c-(39/50)*s)*(25*(1+z^2)^2) := by
      rw [identity]
      exact product
    exact (mul_nonneg_iff_of_pos_right denominator).mp scaled
  · intro sp
    have zp : 0<z := div_pos sp den
    have scaled : 0<(1+c*(c+s)-2*c-(39/50)*s)*(25*(1+z^2)^2) := by
      rw [identity]
      exact mul_pos zp polynomial
    exact (mul_pos_iff_of_pos_right denominator).mp scaled

/-- Both wall gaps, with the second strictly positive even at s=0. -/
theorem wall_gaps (c s r : ℝ) (cp : 0<c) (sn : 0≤s)
    (unit : c^2+s^2=1) (rhigh : r≤39/100) :
    0≤1+c*(c+s)-2*c-2*r*s ∧
      0<1+s*(c+s)-2*s-2*r*c := by
  have first := (gap_nonnegative c s cp.le sn unit).1
  have second := (gap_nonnegative s c sn cp.le (by nlinarith only [unit])).2 cp
  have ds := mul_nonneg sn (sub_nonneg.mpr rhigh)
  have dc := mul_nonneg cp.le (sub_nonneg.mpr rhigh)
  constructor <;> nlinarith only [first,second,ds,dc]

/-- The positive-definite expression in (8); its transpose is used in (11). -/
theorem quadratic_margin (c s : ℝ) (cp : 0<c) (sn : 0≤s) :
    0<(11/100)*c^2+(3/20)*s^2-(1/4)*c*s := by
  by_cases zero : s=0
  · rw [zero]
    nlinarith only [sq_pos_of_pos cp]
  · have sp : 0<s := by
      rcases sn.eq_or_lt with eq | pos
      · exact (zero eq.symm).elim
      · exact pos
    nlinarith only [sq_nonneg (22*c-25*s),sq_pos_of_pos sp]

/-- The transposed expression remains positive because c is positive. -/
theorem quadratic_margin_transpose (c s : ℝ) (cp : 0<c) :
    0<(3/20)*c^2+(11/100)*s^2-(1/4)*c*s := by
  nlinarith only [sq_nonneg (22*s-25*c),sq_pos_of_pos cp]

/-- The small-angle comparison in (9),(10), including its strict endpoint. -/
theorem negative_u_margin (c s r : ℝ) (cp : 0<c) (sp : 0<s)
    (clow : 1-(3/5)*s^2≤c) (rlow : 11/50≤r)
    (small : r*s<(43/500)*c) :
    1<c+(43/500)*s^2+r*c*s := by
  have rp : 0<r := by linarith only [rlow]
  have square : (43/500)*(257/500)<r^2 := by
    nlinarith only [rlow]
  have first := mul_pos (show 0<(43/500)*c-r*s by linarith only [small])
    (by norm_num : (0:ℝ)<257/500)
  have second := mul_pos (sub_pos.mpr square) cp
  have coefficient : 0<r*c-(257/500)*s := by
    have scaled : 0<r*(r*c-(257/500)*s) := by
      nlinarith only [first,second]
    exact (mul_pos_iff_of_pos_left rp).mp scaled
  have strict := mul_pos sp coefficient
  nlinarith only [strict,clow]

end
end N12Compact.WallSignChord
