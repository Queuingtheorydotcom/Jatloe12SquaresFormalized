import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact scalar part of `C1092-MPPM-ORDINARY-NEGATIVE-HALFPOINT.md`.
All canonical endpoints are retained. The quartic is the manuscript's
coefficient-norm certificate, not an orientation subdivision.
Source translation only; no compiler or replay has been run. -/
namespace N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
set_option Elab.async false

structure Frame (c s : ℝ) : Prop where
  positive : 0<c
  nonnegative : 0≤s
  ordered : s≤c
  unit : c^2+s^2=1

private theorem linear_norm (A B c s r : ℝ) (unit : c^2+s^2=1)
    (rp : 0<r) (small : A^2+B^2<r^2) : A*c+B*s<r := by
  have identity : (A*c+B*s)^2+(A*s-B*c)^2=A^2+B^2 := by
    calc
      _ = (A^2+B^2)*(c^2+s^2) := by ring
      _ = _ := by rw [unit,mul_one]
  by_contra no
  have product := mul_nonneg
    (show 0≤A*c+B*s-r by linarith only [no])
    (show 0≤A*c+B*s+r by linarith only [no,rp])
  nlinarith only [identity,sq_nonneg (A*s-B*c),small,product]

theorem relative (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    0<c*d+s*t ∧ (c*d+s*t)^2+(c*t-s*d)^2=1 := by
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos C.positive E.positive)
      (mul_nonneg C.nonnegative E.nonnegative)
  · calc
      _ = (c^2+s^2)*(d^2+t^2) := by ring
      _ = 1 := by rw [C.unit,E.unit]; norm_num

theorem source_coordinates (c s d t : ℝ) (unit : d^2+t^2=1) :
    c=(c*d+s*t)*d+(c*t-s*d)*t ∧
      s=(c*d+s*t)*t-(c*t-s*d)*d := by
  constructor
  · calc
      c = c*(d^2+t^2) := by rw [unit,mul_one]
      _ = _ := by ring
  · calc
      s = s*(d^2+t^2) := by rw [unit,mul_one]
      _ = _ := by ring

private theorem coefficient (c s : ℝ) (unit : c^2+s^2=1) :
    (793/500)*c+s-1<9/10 := by
  have h := linear_norm (793/500) 1 c s (19/10) unit
    (by norm_num) (by norm_num)
  linarith only [h]

/-- Source normal, nonnegative relative angle: manuscript (9). -/
theorem c_positive (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (order : 0≤c*t-s*d) :
    (793/500)*c+s<1+(c*d+s*t) := by
  let k := c*d+s*t
  let delta := c*t-s*d
  have kp : 0<k := (relative c s d t C E).1
  have sum := (CommonCases.CanonicalScalars.bounds d t E.positive
    E.nonnegative E.ordered E.unit).2.2.2.1
  have identity : c+s=k*(d+t)-delta*(d-t) := by
    calc
      _ = (c+s)*(d^2+t^2) := by rw [E.unit,mul_one]
      _ = _ := by dsimp [k,delta]; ring
  have product := mul_nonneg order (sub_nonneg.mpr E.ordered)
  have width := mul_le_mul_of_nonneg_left sum kp.le
  have lower : (7/10)*(c+s)≤k := by
    change 0≤delta*(d-t) at product
    nlinarith only [identity,product,width]
  have norm := linear_norm (443/500) (3/10) c s 1 C.unit
    (by norm_num) (by norm_num)
  change (793/500)*c+s<1+k
  linarith only [lower,norm]

/-- Source normal, nonpositive relative angle: manuscript (10). -/
theorem c_negative (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (order : c*t-s*d≤0) :
    (793/500)*c+s+(c*t-s*d)*((37/50)*d-t/2)<1+(c*d+s*t) := by
  let k := c*d+s*t
  let e := -(c*t-s*d)
  have kp : 0<k := (relative c s d t C E).1
  have en : 0≤e := by dsimp [e]; linarith only [order]
  have unit : k^2+e^2=1 := by
    simpa only [k,e,neg_sq] using (relative c s d t C E).2
  have d1 := (CommonCases.CanonicalScalars.bounds d t E.positive
    E.nonnegative E.ordered E.unit).2.1
  have first := coefficient d t E.unit
  have second : (13/50)*d-(543/500)*t≤13/50 := by
    linarith only [d1,E.nonnegative]
  have firstWeighted := mul_lt_mul_of_pos_right first kp
  have secondWeighted := mul_le_mul_of_nonneg_right second en
  have norm := linear_norm (9/10) (13/50) k e 1 unit
    (by norm_num) (by norm_num)
  have identity :
      (793/500)*c+s+(c*t-s*d)*((37/50)*d-t/2)-k =
        ((793/500)*d+t-1)*k+((13/50)*d-(543/500)*t)*e := by
    dsimp [k,e]
    linear_combination -((793/500)*c+s)*E.unit
  change (793/500)*c+s+(c*t-s*d)*((37/50)*d-t/2)<1+k
  linarith only [identity,firstWeighted,secondWeighted,norm]

/-- Target normal, nonnegative relative angle: manuscript (11). -/
theorem e_positive (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (order : 0≤c*t-s*d) :
    (543/500)*(c*d+s*t)*c+(7/20)*(c*t-s*d)*(c-s)+d/2+t <
      1+(c*d+s*t)+(c*t-s*d) := by
  let k := c*d+s*t
  let delta := c*t-s*d
  have kp : 0<k := (relative c s d t C E).1
  have dn : 0≤delta := order
  have unit : k^2+delta^2=1 := (relative c s d t C E).2
  have c1 := (CommonCases.CanonicalScalars.bounds c s C.positive
    C.nonnegative C.ordered C.unit).2.1
  have first := coefficient c s C.unit
  have second : (27/20)*c-(17/20)*s-1≤7/20 := by
    linarith only [c1,C.nonnegative]
  have firstWeighted := mul_lt_mul_of_pos_right first kp
  have secondWeighted := mul_le_mul_of_nonneg_right second dn
  have norm := linear_norm (9/10) (7/20) k delta 1 unit
    (by norm_num) (by norm_num)
  have identity : (543/500)*k*c+(7/20)*delta*(c-s)+d/2+t-k-delta =
      ((793/500)*c+s-1)*k+((27/20)*c-(17/20)*s-1)*delta := by
    dsimp [k,delta]
    linear_combination -(d/2+t)*C.unit
  change (543/500)*k*c+(7/20)*delta*(c-s)+d/2+t<1+k+delta
  linarith only [identity,firstWeighted,secondWeighted,norm]

/-- The exact quartic certificate (13)--(14), over the whole canonical range. -/
theorem coefficient_norm (c s : ℝ) (C : Frame c s) :
    (1/2-c+(543/500)*c^2+(7/20)*s*(c+s))^2+
      (1-s+(543/500)*c*s-(7/20)*c*(c+s))^2<1 := by
  let x := s/(1+c)
  have den : 0<1+c := by linarith only [C.positive]
  have xn : 0≤x := div_nonneg C.nonnegative den.le
  have relation : x*(1+c)=s := div_mul_cancel₀ _ den.ne'
  have half : s*x=1-c := by
    apply (mul_right_cancel₀ den.ne')
    linear_combination s*relation+C.unit
  have cf : c=(1-x^2)/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*relation+half
  have sf : s=2*x/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*half-relation
  have quadratic : x^2+2*x≤1 := by
    have order := C.ordered
    rw [cf,sf] at order
    have result := (div_le_div_iff_of_pos_right
      (by positivity : (0:ℝ)<1+x^2)).mp order
    linarith only [result]
  have xhigh : x≤5/12 := by
    by_contra no
    have product := mul_nonneg (show 0≤x-5/12 by linarith only [no])
      (show 0≤x+5/12 by linarith only [xn])
    nlinarith only [product,quadratic,no]
  have xsq : x^2≤(5/12)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr xhigh)
      (show 0≤5/12+x by linarith only [xn])]
  have cubic := mul_nonneg (pow_nonneg xn 3)
    (show 0≤1016750-763737*x by linarith only [xhigh])
  have polynomial : 0 < -763737*x^4+1016750*x^3-126776*x^2-16750*x+29263 := by
    nlinarith only [cubic,xsq,xhigh]
  let P := 1/2-c+(543/500)*c^2+(7/20)*s*(c+s)
  let Q := 1-s+(543/500)*c*s-(7/20)*c*(c+s)
  have identity : (1-P^2-Q^2)*(125000*(1+x^2)^2)=
      -763737*x^4+1016750*x^3-126776*x^2-16750*x+29263 := by
    dsimp [P,Q]
    rw [cf,sf]
    field_simp [show (1+x^2:ℝ)≠0 by positivity]
    ring
  have positive : 0<1-P^2-Q^2 := by
    apply (mul_pos_iff_of_pos_right
      (by positivity : (0:ℝ)<125000*(1+x^2)^2)).mp
    rw [identity]
    exact polynomial
  change P^2+Q^2<1
  linarith only [positive]

/-- Target normal, nonpositive relative angle: manuscript (12).
The norm estimate itself does not need the relative-order hypothesis. -/
theorem e_negative (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    d/2+t-(c*d+s*t)*(1-(543/500)*c)+
      (7/20)*(-(c*t-s*d))*(c+s)<1 := by
  have norm := linear_norm
    (1/2-c+(543/500)*c^2+(7/20)*s*(c+s))
    (1-s+(543/500)*c*s-(7/20)*c*(c+s)) d t 1 E.unit
    (by norm_num) (by simpa only [one_pow] using coefficient_norm c s C)
  nlinarith only [norm]

end N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
