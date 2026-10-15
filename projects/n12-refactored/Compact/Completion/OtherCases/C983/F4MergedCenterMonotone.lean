import Compact.Completion.OtherCases.C983.F4MergedCenterPositive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The one-variable monotonicity arguments written in §§4–5 of
`C983-F4-MERGED-CENTER.md`. Angles are ordinary real angles on [0,π/4];
the derivative signs are the manuscript's displayed estimates.
Source only: no compiler replay has been performed. -/
namespace N12Compact.Completion.OtherCases.C983.F4MergedCenter
open S12 S12Pilot Set
set_option Elab.async false
noncomputable section

private theorem quarter_bounds (q : ℝ) (hq : q∈Icc 0 (Real.pi/4)) :
    0<Real.cos q ∧ 0≤Real.sin q ∧ Real.sin q≤Real.cos q ∧
      1≤Real.cos q+Real.sin q ∧ Real.cos q+Real.sin q≤5/3 := by
  have pp := Real.pi_pos
  have cp := Real.cos_pos_of_mem_Ioo
    (show q∈Ioo (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith only [hq.1,hq.2,pp])
  have sn := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith only [hq.2,pp])
  have ordered := Real.cos_le_cos_of_nonneg_of_le_pi hq.1
    (show Real.pi/2-q≤Real.pi by linarith only [hq.1,pp])
    (show q≤Real.pi/2-q by linarith only [hq.2])
  rw [Real.cos_pi_div_two_sub] at ordered
  have unit := Real.sin_sq_add_cos_sq q
  have product := mul_nonneg cp.le sn
  have sum : 1≤Real.cos q+Real.sin q := by nlinarith only [unit,product,cp,sn]
  have sumUpper : Real.cos q+Real.sin q≤5/3 := by
    nlinarith only [unit,sq_nonneg (Real.cos q-Real.sin q)]
  exact ⟨cp,sn,ordered,sum,sumUpper⟩

/-- Canonical normals have the angle representation used in §§4–5. -/
theorem canonical_angle (b t : ℝ) (bp : 0<b) (tn : 0≤t)
    (order : t≤b) (unit : b^2+t^2=1) :
    let q := Real.arctan (t/b)
    q∈Icc 0 (Real.pi/4) ∧ Real.cos q=b ∧ Real.sin q=t := by
  let q := Real.arctan (t/b)
  have qLow : 0≤q := by
    have result := Real.arctan_le_arctan (div_nonneg tn bp.le)
    simpa only [Real.arctan_zero] using result
  have qHigh : q≤Real.pi/4 := by
    have result := Real.arctan_le_arctan ((div_le_one bp).mpr order)
    simpa only [Real.arctan_one] using result
  have cp := Real.cos_arctan_pos (t/b)
  have denominator : 1+(t/b)^2=1/b^2 := by
    field_simp [bp.ne']
    nlinarith only [unit]
  have cosineSquare : (Real.cos q)^2=b^2 := by
    dsimp only [q]
    rw [Real.cos_sq_arctan,denominator,one_div_one_div]
  have cosine : Real.cos q=b := by nlinarith only [cosineSquare,cp,bp]
  have tangent := Real.tan_arctan (t/b)
  rw [Real.tan_eq_sin_div_cos] at tangent
  have sine : Real.sin q=t := by
    change Real.sin q/Real.cos q=t/b at tangent
    rw [cosine] at tangent
    exact (div_left_inj' bp.ne').mp tangent
  exact ⟨⟨qLow,qHigh⟩,cosine,sine⟩

def Bminus (d r q : ℝ) : ℝ :=
  d*(Real.cos q-1)+r*(Real.sin q+(1-Real.sin q)/Real.cos q-43/500)

def Bplus (d r q : ℝ) : ℝ :=
  (d-r)*Real.cos q+(d+r)*Real.sin q-d+r*((1-Real.sin q)/Real.cos q)-(43/500)*r

def G (A B q : ℝ) : ℝ :=
  Real.cos q+Real.sin q-2+A+(1-A)*(Real.sin q)^2+B*(Real.cos q*Real.sin q)

private theorem quotient_derivative (q : ℝ) (cp : 0<Real.cos q) (sn : 0≤Real.sin q) :
    HasDerivAt (fun x => (1-Real.sin x)/Real.cos x) (-1/(1+Real.sin q)) q := by
  have quotient := ((Real.hasDerivAt_sin q).const_sub 1).div
    (Real.hasDerivAt_cos q) cp.ne'
  convert quotient using 1
  have nonzero : 1+Real.sin q≠0 := by linarith only [sn]
  field_simp [cp.ne',nonzero]
  have weighted := congrArg (fun x : ℝ => Real.sin q*x) (Real.sin_sq_add_cos_sq q)
  nlinarith only [Real.sin_sq_add_cos_sq q,weighted]

private theorem Bminus_derivative (d r q : ℝ) (cp : 0<Real.cos q) (sn : 0≤Real.sin q) :
    HasDerivAt (Bminus d r)
      (-d*Real.sin q+r*(Real.cos q-1/(1+Real.sin q))) q := by
  have result := (((Real.hasDerivAt_cos q).sub_const 1).const_mul d).add
    ((((Real.hasDerivAt_sin q).add (quotient_derivative q cp sn)).sub_const (43/500)).const_mul r)
  convert result using 1 <;> dsimp only [Bminus] <;> ring

private theorem Bplus_derivative (d r q : ℝ) (cp : 0<Real.cos q) (sn : 0≤Real.sin q) :
    HasDerivAt (Bplus d r)
      (d*(Real.cos q-Real.sin q)+r*(Real.cos q+Real.sin q-1/(1+Real.sin q))) q := by
  have result := (((((Real.hasDerivAt_cos q).const_mul (d-r)).add
    ((Real.hasDerivAt_sin q).const_mul (d+r))).sub_const d).add
      ((quotient_derivative q cp sn).const_mul r)).sub_const ((43/500)*r)
  convert result using 1 <;> dsimp only [Bplus] <;> ring

private theorem G_derivative (A B q : ℝ) :
    HasDerivAt (G A B)
      (Real.cos q-Real.sin q+2*(1-A)*Real.sin q*Real.cos q+
        B*((Real.cos q)^2-(Real.sin q)^2)) q := by
  have result := (((((Real.hasDerivAt_cos q).add (Real.hasDerivAt_sin q)).sub_const 2).add_const A).add
    (((Real.hasDerivAt_sin q).pow 2).const_mul (1-A))).add
      (((Real.hasDerivAt_cos q).mul (Real.hasDerivAt_sin q)).const_mul B)
  convert result using 1 <;> dsimp only [G] <;> ring

/-- The displayed derivative B₋'≤(r-d)sin(q)≤0. -/
theorem Bminus_antitone (d r : ℝ) (rn : 0≤r) (order : r≤d) :
    AntitoneOn (Bminus d r) (Icc 0 (Real.pi/4)) := by
  have derivative (q : ℝ) (hq : q∈Icc 0 (Real.pi/4)) :=
    Bminus_derivative d r q (quarter_bounds q hq).1 (quarter_bounds q hq).2.1
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro q hq
    exact (derivative q hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (derivative q (interior_subset hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    have bounds := quarter_bounds q (interior_subset hq)
    rw [(derivative q (interior_subset hq)).deriv]
    have denominator : 0<1+Real.sin q := by linarith only [bounds.2.1]
    have inverse : 1-Real.sin q≤1/(1+Real.sin q) :=
      (le_div_iff₀ denominator).mpr (by nlinarith only [sq_nonneg (Real.sin q)])
    have cosine := Real.cos_le_one q
    have weighted := mul_nonneg rn
      (show 0≤Real.sin q-(Real.cos q-1/(1+Real.sin q)) by linarith only [inverse,cosine])
    have last := mul_nonneg (sub_nonneg.mpr order) bounds.2.1
    nlinarith only [weighted,last]

/-- The two nonnegative summands of the displayed B₊' formula. -/
theorem Bplus_monotone (d r : ℝ) (dn : 0≤d) (rn : 0≤r) :
    MonotoneOn (Bplus d r) (Icc 0 (Real.pi/4)) := by
  have derivative (q : ℝ) (hq : q∈Icc 0 (Real.pi/4)) :=
    Bplus_derivative d r q (quarter_bounds q hq).1 (quarter_bounds q hq).2.1
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro q hq
    exact (derivative q hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (derivative q (interior_subset hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    have bounds := quarter_bounds q (interior_subset hq)
    rw [(derivative q (interior_subset hq)).deriv]
    have inverse : 1/(1+Real.sin q)≤1 :=
      (div_le_one (by linarith only [bounds.2.1])).mpr (by linarith only [bounds.2.1])
    have first := mul_nonneg dn (sub_nonneg.mpr bounds.2.2.1)
    have last := mul_nonneg rn
      (show 0≤Real.cos q+Real.sin q-1/(1+Real.sin q) by linarith only [bounds.2.2.2.1,inverse])
    linarith only [first,last]

/-- The derivative estimate for G₋ in §5.1. -/
theorem G_antitone (A B : ℝ) (a : 1≤A) (b : B≤ -1) :
    AntitoneOn (G A B) (Icc 0 (Real.pi/4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro q _
    exact (G_derivative A B q).continuousAt.continuousWithinAt
  · intro q _
    exact (G_derivative A B q).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [(G_derivative A B q).deriv]
    obtain ⟨cp,sn,order,sum,sumUpper⟩ := quarter_bounds q (interior_subset hq)
    have square := (sq_le_sq₀ sn cp.le).mpr order
    have first := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr a) (mul_nonneg sn cp.le)
    have second := mul_nonpos_of_nonpos_of_nonneg (show B+1≤0 by linarith only [b])
      (sub_nonneg.mpr square)
    have third := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr order)
      (show 1-Real.cos q-Real.sin q≤0 by linarith only [sum])
    nlinarith only [first,second,third]

/-- The derivative estimate for G₊ in §5.2. -/
theorem G_monotone (A B : ℝ) (a : A≤1) (b : -(3/5)≤B) :
    MonotoneOn (G A B) (Icc 0 (Real.pi/4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro q _
    exact (G_derivative A B q).continuousAt.continuousWithinAt
  · intro q _
    exact (G_derivative A B q).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [(G_derivative A B q).deriv]
    obtain ⟨cp,sn,order,sum,sumUpper⟩ := quarter_bounds q (interior_subset hq)
    have square := (sq_le_sq₀ sn cp.le).mpr order
    have first := mul_nonneg (sub_nonneg.mpr a) (mul_nonneg sn cp.le)
    have second := mul_nonneg (show 0≤B+3/5 by linarith only [b]) (sub_nonneg.mpr square)
    have third := mul_nonneg (sub_nonneg.mpr order)
      (show 0≤1-(3/5)*(Real.cos q+Real.sin q) by linarith only [sumUpper])
    nlinarith only [first,second,third]

private theorem Bminus_normal (d r b t q : ℝ) (bp : 0<b)
    (cosine : Real.cos q=b) (sine : Real.sin q=t) :
    Bminus d r q=(d*b+r*t)+(r-(d*b+r*t))/b-(43/500)*r := by
  rw [Bminus,cosine,sine]
  field_simp [bp.ne']
  ring

private theorem Bplus_normal (d r b t q : ℝ) (bp : 0<b)
    (cosine : Real.cos q=b) (sine : Real.sin q=t) :
    Bplus d r q=(d*b+r*t)+(r-(d*b+r*t))/b-(43/500)*r+(d*t-r*b) := by
  rw [Bplus,cosine,sine]
  field_simp [bp.ne']
  ring

private theorem G_normal (A B b t q : ℝ) (unit : b^2+t^2=1)
    (cosine : Real.cos q=b) (sine : Real.sin q=t) :
    G A B q=b+t-1+(A-1)*b^2+B*b*t := by
  rw [G,cosine,sine]
  linear_combination -(A-1)*unit

private theorem Gminus_normal (d r b t q : ℝ) (bp : 0<b)
    (unit : b^2+t^2=1) (cosine : Real.cos q=b) (sine : Real.sin q=t) :
    G (d+(7/20)*r*(d+r)) (r-1-43/500-(7/20)*d*(d+r)) q=
      b*(1-b-t+(t-1)/b-(43/500)*t+(d*b+r*t)+(7/20)*(r*b-d*t)*(d+r)) := by
  rw [G_normal _ _ b t q unit cosine sine]
  field_simp [bp.ne']
  ring

private theorem Gplus_normal (d r b t q : ℝ) (bp : 0<b)
    (unit : b^2+t^2=1) (cosine : Real.cos q=b) (sine : Real.sin q=t) :
    G (d-(7/20)*r*(d-r)) (r-1-43/500+(7/20)*d*(d-r)) q=
      b*(1-b-t+(t-1)/b-(43/500)*t+(d*b+r*t)+(7/20)*(d*t-r*b)*(d-r)) := by
  rw [G_normal _ _ b t q unit cosine sine]
  field_simp [bp.ne']
  ring

/-- All four monotonicity conclusions, instantiated with precisely the
half-angle window and coarse bounds proved in manuscript §§1–2. -/
theorem positive_comparisons (d r z : ℝ)
    (dp : 0<d) (rp : 0<r) (order : r≤d) (unit : d^2+r^2=1)
    (short : r*z=1-d) (relation : z*(1+d)=r)
    (zLower : 1/4<z) (zUpper : z<13/50)
    (dLower : 87/100<d) (rLower : 47/100<r) (rUpper : r<49/100)
    (sumLower : 27/20<d+r) (diffLower : 19/50<d-r) :
    PositiveComparisons d r := by
  let p := Real.arctan (r/d)
  obtain ⟨pRange,pc,ps⟩ := canonical_angle d r dp rp.le order unit
  have margin := joining_margin d r z dp rp unit short relation zLower.le zUpper.le
  have joinMinus : Bminus d r p=1+(r-1)/d-(43/500)*r := by
    rw [Bminus_normal d r d r p dp pc ps]
    rw [show d*d+r*r=1 by nlinarith only [unit]]
  have joinPlus : Bplus d r p=1+(r-1)/d-(43/500)*r := by
    rw [Bplus_normal d r d r p dp pc ps]
    rw [show d*d+r*r=1 by nlinarith only [unit],show d*r-r*d=0 by ring]
    ring
  have aMinus : 1≤d+(7/20)*r*(d+r) := by
    have product := mul_pos rp (show 0<(7/20)*(d+r)-z by linarith only [sumLower,zUpper])
    nlinarith only [product,short]
  have bMinus : r-1-43/500-(7/20)*d*(d+r)≤ -1 := by
    have first := mul_pos (sub_pos.mpr dLower) (show 0<d+r by linarith only [dp,rp])
    have second := mul_pos (show (0:ℝ)<87/100 by norm_num) (sub_pos.mpr sumLower)
    nlinarith only [first,second,rUpper]
  have aPlus : d-(7/20)*r*(d-r)≤1 := by
    have dSmall : d≤1 := by nlinarith only [unit,sq_nonneg r,dp]
    have product := mul_pos rp (show 0<d-r by linarith only [diffLower])
    nlinarith only [dSmall,product]
  have bPlus : -(3/5)≤r-1-43/500+(7/20)*d*(d-r) := by
    have first := mul_pos (sub_pos.mpr dLower) (show 0<d-r by linarith only [diffLower])
    have second := mul_pos (show (0:ℝ)<87/100 by norm_num) (sub_pos.mpr diffLower)
    nlinarith only [first,second,rLower]
  have joinGminus : 0<G (d+(7/20)*r*(d+r)) (r-1-43/500-(7/20)*d*(d+r)) p := by
    rw [Gminus_normal d r d r p dp unit pc ps]
    have identity :
        1-d-r+(r-1)/d-(43/500)*r+(d*d+r*r)+(7/20)*(r*d-d*r)*(d+r)=
        1+(r-1)/d-(43/500)*r-(d+r-1) := by nlinarith only [unit]
    rw [identity]
    exact mul_pos dp margin
  have joinGplus : 0<G (d-(7/20)*r*(d-r)) (r-1-43/500+(7/20)*d*(d-r)) p := by
    rw [Gplus_normal d r d r p dp unit pc ps]
    have identity :
        1-d-r+(r-1)/d-(43/500)*r+(d*d+r*r)+(7/20)*(d*r-r*d)*(d-r)=
        1+(r-1)/d-(43/500)*r-(d+r-1) := by nlinarith only [unit]
    rw [identity]
    exact mul_pos dp margin
  constructor
  · intro b t bp tn canonical ku
    let q := Real.arctan (t/b)
    obtain ⟨qRange,qc,qs⟩ := canonical_angle b t bp tn canonical ku
    by_cases relative : d*t-r*b≤0
    · have angleOrder : q≤p := Real.arctan_le_arctan
        ((div_le_div_iff₀ bp dp).mpr (by linarith only [relative]))
      have bound := Bminus_antitone d r rp.le order qRange pRange angleOrder
      rw [joinMinus,Bminus_normal d r b t q bp qc qs] at bound
      simpa only [max_eq_right relative,add_zero] using bound
    · have relative' : 0≤d*t-r*b := by linarith only [relative]
      have angleOrder : p≤q := Real.arctan_le_arctan
        ((div_le_div_iff₀ dp bp).mpr (by linarith only [relative']))
      have bound := Bplus_monotone d r dp.le rp.le pRange qRange angleOrder
      rw [joinPlus,Bplus_normal d r b t q bp qc qs] at bound
      simpa only [max_eq_left relative'] using bound
  · intro b t bp tn canonical ku relative
    let q := Real.arctan (t/b)
    obtain ⟨qRange,qc,qs⟩ := canonical_angle b t bp tn canonical ku
    have angleOrder : q≤p := Real.arctan_le_arctan
      ((div_le_div_iff₀ bp dp).mpr (by linarith only [relative]))
    have bound := G_antitone _ _ aMinus bMinus qRange pRange angleOrder
    have positive := lt_of_lt_of_le joinGminus bound
    rw [Gminus_normal d r b t q bp ku qc qs] at positive
    exact (mul_pos_iff_of_pos_left bp).mp positive
  · intro b t bp tn canonical ku relative
    let q := Real.arctan (t/b)
    obtain ⟨qRange,qc,qs⟩ := canonical_angle b t bp tn canonical ku
    have angleOrder : p≤q := Real.arctan_le_arctan
      ((div_le_div_iff₀ dp bp).mpr (by linarith only [relative]))
    have bound := G_monotone _ _ aPlus bPlus pRange qRange angleOrder
    have positive := lt_of_lt_of_le joinGplus bound
    rw [Gplus_normal d r b t q bp ku qc qs] at positive
    exact (mul_pos_iff_of_pos_left bp).mp positive

end
#print axioms Bminus_antitone
#print axioms Bplus_monotone
#print axioms G_antitone
#print axioms G_monotone
#print axioms positive_comparisons
end N12Compact.Completion.OtherCases.C983.F4MergedCenter
