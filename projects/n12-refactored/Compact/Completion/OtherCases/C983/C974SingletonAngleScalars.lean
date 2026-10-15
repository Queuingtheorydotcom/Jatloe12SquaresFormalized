import Compact.Completion.OtherCases.C983.C974SingletonSign
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The completed calculus estimate in MISSING-CORNER-MIDPOINT §1.4.
The endpoint is written sqrt(4/13), exactly 2/sqrt(13). Every comparison
uses the full interval, including both endpoints. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open Set
set_option Elab.async false
noncomputable section

private def D (t : ℝ) := Real.sqrt (1-t^2)
private def G (t : ℝ) := (7/4)*D t-(11/8)*(D t)^2-(1/4)*D t*t-t/4
private def G1 (t : ℝ) := (11/4)*t-1/4+(2*t^2-7*t-1)/(4*D t)
private def Q (t : ℝ) := 11*(D t)^3-7+3*t-2*t^3
private def Q1 (t : ℝ) := -33*t*D t+3-6*t^2
private def Q2 (t : ℝ) := -33*(D t-t^2/D t)-12*t
private def endpoint : ℝ := Real.sqrt (4/13)

private theorem endpoint_pos : 0<endpoint := Real.sqrt_pos.2 (by norm_num)
private theorem endpoint_square : endpoint^2=4/13 := Real.sq_sqrt (by norm_num)

private theorem interval_data (t : ℝ) (ht : t∈Icc 0 endpoint) :
    0<1-t^2 ∧ 0<D t ∧ (D t)^2=1-t^2 ∧ t^2≤4/13 := by
  have product := mul_nonneg (sub_nonneg.mpr ht.2)
    (show 0≤endpoint+t by linarith only [endpoint_pos,ht.1])
  have square : t^2≤4/13 := by nlinarith only [product,endpoint_square]
  have positive : 0<1-t^2 := by linarith only [square]
  exact ⟨positive,Real.sqrt_pos.2 positive,Real.sq_sqrt positive.le,square⟩

private theorem derivative_D (t : ℝ) (ht : 0<1-t^2) : HasDerivAt D (-t/D t) t := by
  have result := (((hasDerivAt_id t).pow 2).const_sub 1).sqrt ht.ne'
  have dn : Real.sqrt (1-t^2)≠0 := (Real.sqrt_pos.2 ht).ne'
  convert result using 1 <;> dsimp only [D] <;> field_simp [dn] <;> ring

private theorem derivative_G (t : ℝ) (ht : 0<1-t^2) : HasDerivAt G (G1 t) t := by
  have dp : 0<D t := Real.sqrt_pos.2 ht
  have square : (D t)^2=1-t^2 := Real.sq_sqrt ht.le
  have dd := derivative_D t ht
  have result := ((((dd.const_mul (7/4)).sub ((dd.pow 2).const_mul (11/8))).sub
    ((dd.mul (hasDerivAt_id t)).const_mul (1/4))).sub ((hasDerivAt_id t).div_const 4)
  convert result using 1 <;> dsimp only [G,G1]
  all_goals first | (ext q; ring) | (field_simp [dp.ne']; nlinarith only [square])

private theorem derivative_G1 (t : ℝ) (ht : 0<1-t^2) :
    HasDerivAt G1 (Q t/(4*(D t)^3)) t := by
  have dp : 0<D t := Real.sqrt_pos.2 ht
  have square : (D t)^2=1-t^2 := Real.sq_sqrt ht.le
  have dd := derivative_D t ht
  have numerator := ((((hasDerivAt_id t).pow 2).const_mul 2).sub
    ((hasDerivAt_id t).const_mul 7)).sub_const 1
  have result := (((hasDerivAt_id t).const_mul (11/4)).sub_const (1/4)).add
    (numerator.div (dd.const_mul 4) (by positivity))
  convert result using 1 <;> dsimp only [G1,Q]
  all_goals first | (ext q; ring) | (field_simp [dp.ne']; nlinarith only [square,
    show t*(D t)^2=t*(1-t^2) by rw [square]])

private theorem derivative_Q (t : ℝ) (ht : 0<1-t^2) : HasDerivAt Q (Q1 t) t := by
  have dp : 0<D t := Real.sqrt_pos.2 ht
  have result := (((((derivative_D t ht).pow 3).const_mul 11).sub_const 7).add
    ((hasDerivAt_id t).const_mul 3)).sub (((hasDerivAt_id t).pow 3).const_mul 2)
  convert result using 1 <;> dsimp only [Q,Q1]
  all_goals first | (ext q; ring) | (field_simp [dp.ne']; ring)

private theorem derivative_Q1 (t : ℝ) (ht : 0<1-t^2) : HasDerivAt Q1 (Q2 t) t := by
  have result := ((((hasDerivAt_id t).mul (derivative_D t ht)).const_mul (-33)).add_const 3).sub
    (((hasDerivAt_id t).pow 2).const_mul 6)
  convert result using 1 <;> dsimp only [Q1,Q2]
  all_goals first | (ext q; ring) | ring

private theorem Q2_negative (t : ℝ) (ht : t∈Icc 0 endpoint) : Q2 t<0 := by
  obtain ⟨_,dp,square,bound⟩ := interval_data t ht
  have quotient : t^2/D t<D t := (div_lt_iff₀ dp).mpr (by nlinarith only [square,bound])
  dsimp only [Q2]
  linarith only [quotient,ht.1]

private theorem endpoint_values :
    Q endpoint=(359/26)*endpoint-7 ∧
      G1 endpoint=(61/24)*endpoint-17/12 ∧
      G endpoint-1/4=(19/8)*endpoint-137/104 := by
  have b := endpoint_pos
  have square := endpoint_square
  have ds : D endpoint=3*endpoint/2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by nlinarith only [square]) (by positivity)).mpr
    nlinarith only [square]
  have cube : endpoint^3=(4/13)*endpoint := by
    calc
      endpoint^3=endpoint*endpoint^2 := by ring
      _=(4/13)*endpoint := by rw [square]; ring
  refine ⟨?_,?_,?_⟩
  · dsimp only [Q]
    rw [ds]
    nlinarith only [cube]
  · dsimp only [G1]
    rw [ds]
    field_simp [b.ne']
    nlinarith only [square]
  · dsimp only [G]
    rw [ds]
    nlinarith only [square]

private theorem Q_positive (t : ℝ) (ht : t∈Icc 0 endpoint) : 0<Q t := by
  have concave : ConcaveOn ℝ (Icc 0 endpoint) Q := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (f':=Q1) (f'':=Q2) (convex_Icc _ _)
    · intro q hq
      exact (derivative_Q q (interval_data q hq).1).continuousAt.continuousWithinAt
    · intro q hq
      exact (derivative_Q q (interval_data q (interior_subset hq)).1).hasDerivWithinAt
    · intro q hq
      exact (derivative_Q1 q (interval_data q (interior_subset hq)).1).hasDerivWithinAt
    · intro q hq
      exact (Q2_negative q (interior_subset hq)).le
  have first : 0<Q 0 := by norm_num [Q,D]
  have last : 0<Q endpoint := by
    rw [endpoint_values.1]
    nlinarith only [endpoint_square,endpoint_pos]
  have bn : 0≤t/endpoint := div_nonneg ht.1 endpoint_pos.le
  have bu : t/endpoint≤1 := (div_le_one endpoint_pos).mpr ht.2
  have bound := concave.ge_on_segment'
    (show (0:ℝ)∈Icc 0 endpoint by exact ⟨le_rfl,endpoint_pos.le⟩)
    (show endpoint∈Icc 0 endpoint by exact ⟨endpoint_pos.le,le_rfl⟩)
    (show 0≤1-t/endpoint by linarith only [bu]) bn
    (show 1-t/endpoint+t/endpoint=1 by ring)
  have point : (1-t/endpoint)*0+(t/endpoint)*endpoint=t := by
    rw [mul_zero,zero_add,div_mul_cancel₀ _ endpoint_pos.ne']
  simp only [smul_eq_mul,point] at bound
  exact lt_of_lt_of_le (lt_min first last) bound

private theorem G_lower (t : ℝ) (ht : t∈Icc 0 endpoint) : 1/4<G t := by
  have increasing : MonotoneOn G1 (Icc 0 endpoint) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f':=fun q => Q q/(4*(D q)^3)) (convex_Icc _ _)
    · intro q hq
      exact (derivative_G1 q (interval_data q hq).1).continuousAt.continuousWithinAt
    · intro q hq
      exact (derivative_G1 q (interval_data q (interior_subset hq)).1).hasDerivWithinAt
    · intro q hq
      have interval := interior_subset hq
      exact (div_pos (Q_positive q interval) (by have dp := (interval_data q interval).2.1; positivity)).le
  have endNegative : G1 endpoint<0 := by
    rw [endpoint_values.2.1]
    nlinarith only [endpoint_square,endpoint_pos]
  have decreasing : AntitoneOn G (Icc 0 endpoint) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=G1) (convex_Icc _ _)
    · intro q hq
      exact (derivative_G q (interval_data q hq).1).continuousAt.continuousWithinAt
    · intro q hq
      exact (derivative_G q (interval_data q (interior_subset hq)).1).hasDerivWithinAt
    · intro q hq
      have interval := interior_subset hq
      have bound := increasing interval ⟨endpoint_pos.le,le_rfl⟩ interval.2
      exact le_of_lt (lt_of_le_of_lt bound endNegative)
  have endpointGap : 1/4<G endpoint := by
    have value := endpoint_values.2.2
    nlinarith only [value,endpoint_square,endpoint_pos]
  exact lt_of_lt_of_le endpointGap (decreasing ht ⟨endpoint_pos.le,le_rfl⟩ ht.2)

/-- Equation (14), with d supplied by the actual W unit normal rather
than by an independent numerical angle parameter. -/
theorem singleton_angle_G (d t : ℝ) (dp : 0<d) (tn : 0≤t)
    (unit : d^2+t^2=1) (slope : 3*t≤2*d) :
    1/4<(7/4)*d-(11/8)*d^2-(1/4)*d*t-t/4 := by
  have scaled := mul_nonneg (sub_nonneg.mpr slope) (show 0≤2*d+3*t by positivity)
  have t2 : t^2≤4/13 := by nlinarith only [scaled,unit]
  have interval : t∈Icc 0 endpoint := by
    refine ⟨tn,?_⟩
    nlinarith only [t2,endpoint_square,endpoint_pos,tn]
  have same : D t=d := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by nlinarith only [unit]) dp.le).mpr
    nlinarith only [unit]
  have result := G_lower t interval
  simpa only [G,same] using result

end
#print axioms singleton_angle_G
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
