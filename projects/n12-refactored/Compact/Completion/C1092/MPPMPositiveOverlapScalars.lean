import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars

/-! Exact scalar comparisons for the centered positive overlap. The
centered-inward chapter's southeast calculation is combined with the
already proved ordinary-forward cap H≤s. This removes its separate
northwest-neighbor quartic argument. No side upper bound is used. -/
namespace N12Compact.C1092MPPMPositiveOverlap
open C1092MPPMOrdinaryNegativeHalfpoint C1092MPPMNonpositivePredecessor
set_option Elab.async false

theorem first_exit (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (tp : 0<t) :
    (c*d-s*t)*(d+(2/5)*t)+(c*t+s*d)*t < (c*d-s*t)+(c*t+s*d) := by
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have dt := mul_pos E.positive tp
  have first : 1-d-t+(2/5)*d*t<0 := by nlinarith only [eb.2.2.2.2,dt]
  have second : t-d-(2/5)*t^2≤0 := by nlinarith only [E.ordered,sq_nonneg t]
  have a := mul_neg_of_pos_of_neg C.positive first
  have b := mul_nonpos_of_nonneg_of_nonpos C.nonnegative second
  have identity : (c*d-s*t)*(d+(2/5)*t)+(c*t+s*d)*t-
      ((c*d-s*t)+(c*t+s*d)) =
      c*(1-d-t+(2/5)*d*t)+s*(t-d-(2/5)*t^2) := by
    linear_combination c*E.unit
  linarith only [identity,a,b]

theorem first_target (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (tp : 0<t) :
    d+(2/5)*t+(7/20)*(c*t+s*d)*(c+s)<1+c*t+s*d := by
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have q : 0≤1-(7/20)*(c+s) := by linarith only [cb.2.2.2.1]
  have order := mul_nonneg C.nonnegative (sub_nonneg.mpr E.ordered)
  have weighted := mul_nonneg (show 0≤c*t+s*d-t*(c+s) by nlinarith only [order]) q
  have arc := mul_nonneg (show 0≤c+s-1 by linarith only [cb.2.2.1])
    (show 0≤13/20-(7/20)*(c+s) by linarith only [cb.2.2.2.1])
  have width := mul_nonneg E.nonnegative
    (show 0≤(c+s)*(1-(7/20)*(c+s))-13/20 by nlinarith only [arc])
  nlinarith only [weighted,width,eb.2.1,tp]

theorem final_source (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (tp : 0<t) :
    (c*d-s*t)*(d+t)+(c*t+s*d)*(t-(2/5)*d)<(c*d-s*t)+(c*t+s*d) := by
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have dt := mul_pos E.positive tp
  have first : 1-d-t+(3/5)*d*t<0 := by nlinarith only [eb.2.2.2.2,dt]
  have second : t-d-2/5-(3/5)*t^2≤0 := by nlinarith only [E.ordered,sq_nonneg t]
  have a := mul_neg_of_pos_of_neg C.positive first
  have b := mul_nonpos_of_nonneg_of_nonpos C.nonnegative second
  have identity : (c*d-s*t)*(d+t)+(c*t+s*d)*(t-(2/5)*d)-
      ((c*d-s*t)+(c*t+s*d)) =
      c*(1-d-t+(3/5)*d*t)+s*(t-d-2/5-(3/5)*t^2) := by
    linear_combination (c-(2/5)*s)*E.unit
  linarith only [identity,a,b]

/-- Section 4's whole-arc coefficient norm forces c+s<1.13. -/
theorem shallow (c s d t H : ℝ) (C : Frame c s) (E : Frame d t)
    (cap : H≤(7/20)*(c+s))
    (necessary : 1+c*t+s*d<d+t+(c*t+s*d)*H) : c+s<113/100 ∧ s<7/50 := by
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have jn : 0≤c*t+s*d := (C1092MPPMNonpositivePredecessor.relative c s d t C E).2
  have weighted := mul_le_mul_of_nonneg_left cap jn
  let q := 1-(7/20)*(c+s)
  let P := 1-s*q
  let Q := 1-c*q
  have value : 1<P*d+Q*t := by dsimp [P,Q,q]; nlinarith only [necessary,weighted]
  have normIdentity : (P*d+Q*t)^2+(P*t-Q*d)^2=P^2+Q^2 := by
    calc
      _ = (P^2+Q^2)*(d^2+t^2) := by ring
      _ = _ := by rw [E.unit,mul_one]
  have product := mul_pos (show 0<P*d+Q*t-1 by linarith only [value])
    (show 0<P*d+Q*t+1 by linarith only [value])
  have polyIdentity : P^2+Q^2-1=2-(27/10)*(c+s)+(329/400)*(c+s)^2 := by
    dsimp [P,Q,q]
    linear_combination (1-(7/20)*(c+s))^2*C.unit
  have polynomial : 0<2-(27/10)*(c+s)+(329/400)*(c+s)^2 := by
    nlinarith only [normIdentity,product,sq_nonneg (P*t-Q*d),polyIdentity]
  have sum : c+s<113/100 := by
    by_contra no
    have monotone := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤c+s-113/100 by linarith only [no])
      (show -(27/10)+(329/400)*(c+s+113/100)≤0 by linarith only [cb.2.2.2.1])
    nlinarith only [monotone,polynomial]
  have small : s<7/50 := by
    by_contra no
    have sh : s<113/200 := by linarith only [sum,C.ordered]
    have first := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤s-7/50 by linarith only [no])
      (show s+7/50-113/100≤0 by linarith only [sh])
    have second := mul_pos (show 0<113/100-s-c by linarith only [sum])
      (show 0<113/100-s+c by linarith only [sum,C.positive])
    nlinarith only [first,second,C.unit]
  exact ⟨sum,small⟩

/-- On the resulting shallow interval, the genuine preceding-origin cap
H≤s already contradicts the last actual southeast separating source. -/
theorem last_impossible (c s d t H : ℝ) (C : Frame c s) (E : Frame d t)
    (cap : H≤(7/20)*(c+s)) (ordinaryCap : H≤s)
    (necessary : 1+c*t+s*d<d+t+(c*t+s*d)*H) : False := by
  have small := (shallow c s d t H C E cap necessary).2
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  let P := 1-s+s^2
  let Q := 1-c+c*s
  have pn : 0≤P := by dsimp [P]; nlinarith only [small,sq_nonneg s]
  have qn : 0≤Q := by dsimp [Q]; nlinarith only [cb.2.1,mul_nonneg C.positive.le C.nonnegative]
  have ph : P≤1-(4/5)*s := by
    have product := mul_nonneg C.nonnegative (show 0≤1/5-s by linarith only [small])
    dsimp [P]; nlinarith only [product]
  have qh : Q≤2*s := by
    have product := mul_nonneg C.nonnegative (sub_nonneg.mpr cb.2.1)
    dsimp [Q]; nlinarith only [product,cb.2.2.1]
  have first := mul_nonneg (sub_nonneg.mpr ph)
    (show 0≤1-(4/5)*s+P by linarith only [ph,pn])
  have second := mul_nonneg (sub_nonneg.mpr qh)
    (show 0≤2*s+Q by linarith only [C.nonnegative,qn])
  have residual := mul_nonneg C.nonnegative
    (show 0≤8/5-(116/25)*s by linarith only [small])
  have norm : P^2+Q^2≤1 := by nlinarith only [first,second,residual]
  have bound := norm_le P Q d t 1 E.unit (by norm_num) (by simpa only [one_pow] using norm)
  have weighted := mul_le_mul_of_nonneg_left ordinaryCap
    (C1092MPPMNonpositivePredecessor.relative c s d t C E).2
  dsimp [P,Q] at bound
  nlinarith only [necessary,weighted,bound]

end N12Compact.C1092MPPMPositiveOverlap
