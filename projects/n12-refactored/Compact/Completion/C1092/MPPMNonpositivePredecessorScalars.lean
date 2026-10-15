import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpointScalars

/-! Scalar comparisons from C1092-MIXED-NEGATIVE-H, sections 4--7, also
used verbatim by C1092-MPPM-POSITIVE-MISSING-NEGATIVE-H. Rational bounds
on the whole canonical arc replace the displayed square-root estimates.
All zero-sine and diagonal endpoints are included. Source only. -/
namespace N12Compact.C1092MPPMNonpositivePredecessor
open C1092MPPMOrdinaryNegativeHalfpoint
set_option Elab.async false

theorem norm_lt (A B c s r : ℝ) (unit : c^2+s^2=1)
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

theorem norm_le (A B c s r : ℝ) (unit : c^2+s^2=1)
    (rp : 0<r) (small : A^2+B^2≤r^2) : A*c+B*s≤r := by
  have identity : (A*c+B*s)^2+(A*s-B*c)^2=A^2+B^2 := by
    calc
      _ = (A^2+B^2)*(c^2+s^2) := by ring
      _ = _ := by rw [unit,mul_one]
  by_contra no
  have product := mul_pos
    (show 0<A*c+B*s-r by linarith only [no])
    (show 0<A*c+B*s+r by linarith only [no,rp])
  nlinarith only [identity,sq_nonneg (A*s-B*c),small,product]

theorem relative (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    0≤c*d-s*t ∧ 0≤c*t+s*d := by
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr C.ordered) E.positive.le,
      mul_nonneg C.nonnegative (sub_nonneg.mpr E.ordered)]
  · exact add_nonneg (mul_nonneg C.positive.le E.nonnegative)
      (mul_nonneg C.nonnegative E.positive.le)

/-- The source's negative transverse normal is impossible in every regime. -/
theorem transverse (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    (63/50)*c+(3/2)*s-(c*d-s*t)*((37/50)*d-t/2)<1+c*t+s*d := by
  let A := 13/25-t+(37/50)*t^2+d*t/2
  let B := 1-d+d^2/2+(37/50)*d*t
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have linear := norm_lt (1/2) (37/50) d t (9/10) E.unit (by norm_num) (by norm_num)
  have aBound : A≤13/25 := by
    have product := mul_nonneg E.nonnegative
      (show 0≤1-((37/50)*t+d/2) by linarith only [linear])
    dsimp [A]
    nlinarith only [product]
  have bLow : 1/2≤B := by
    dsimp [B]
    nlinarith only [sq_nonneg (d-1),mul_nonneg E.positive.le E.nonnegative]
  have sumBound : A+B<69/50 := by
    have first := mul_nonneg (show 0≤10/7-(d+t) by linarith only [eb.2.2.2.1])
      (show 0≤(31/50)*(10/7+d+t)-1 by linarith only [eb.2.2.1])
    have second := mul_nonneg (show 0≤d+t by linarith only [E.positive,E.nonnegative])
      (sub_nonneg.mpr E.ordered)
    dsimp [A,B]
    nlinarith only [first,second,E.unit]
  have bound : A*c+B*s<1 := by
    by_cases order : B≤A
    · have first := mul_le_mul_of_nonneg_right aBound C.positive.le
      have second := mul_le_mul_of_nonneg_right (le_trans order aBound) C.nonnegative
      linarith only [first,second,cb.2.2.2.1]
    · have opposite := mul_nonneg (sub_nonneg.mpr C.ordered)
        (show 0≤B-A by linarith only [order])
      have strict := mul_lt_mul_of_pos_right sumBound
        (show 0<c+s by linarith only [C.positive,C.nonnegative])
      nlinarith only [opposite,strict,cb.2.2.2.1]
  have identity : (63/50)*c+(3/2)*s-(c*d-s*t)*((37/50)*d-t/2)
      -(c*t+s*d)=A*c+B*s := by
    dsimp [A,B]
    linear_combination -(37/50*c+s/2)*E.unit
  linarith only [identity,bound]

theorem first_source (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    (3/2)*c-(6/25)*(c*t+s*d)*t<1+c*d-s*t := by
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have ordered := mul_nonneg (sub_nonneg.mpr E.ordered)
    (show 0≤d+t by linarith only [E.positive,E.nonnegative])
  have tHigh : t<5/7 := by nlinarith only [E.unit,ordered,sq_nonneg (t-5/7)]
  have first : 3/2-d-(6/25)*t^2<4/5 := by nlinarith only [eb.1,sq_nonneg t]
  have second : t*(1-(6/25)*d)<3/5 := by
    have product := mul_nonneg E.nonnegative (show 0≤d-7/10 by linarith only [eb.1])
    nlinarith only [product,tHigh]
  have weighted1 := mul_lt_mul_of_pos_right first C.positive
  have weighted2 := mul_le_mul_of_nonneg_right second.le C.nonnegative
  have norm := norm_le (4/5) (3/5) c s 1 C.unit (by norm_num) (by norm_num)
  nlinarith only [weighted1,weighted2,norm]

theorem first_target (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    (3/2)*d+(63/50)*c*(c*t+s*d)<1+(c*d-s*t)+(c*t+s*d) := by
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have sumHigh : c+s<99/70 := by
    simpa only [one_mul] using norm_lt 1 1 c s (99/70) C.unit (by norm_num) (by norm_num)
  have quadratic := mul_nonneg (show 0≤99/70-(c+s) by linarith only [sumHigh])
    (show 0≤(63/100)*(99/70+c+s)-1 by linarith only [cb.2.2.1])
  have first : 3/2-c-s+(63/50)*c*s<18/25 := by
    nlinarith only [quadratic,C.unit]
  have ordered := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr C.ordered)
    (show (63/100)*(c+s)-1≤0 by linarith only [cb.2.2.2.1])
  have second : s-c+(63/50)*c^2≤63/100 := by nlinarith only [ordered,C.unit]
  have weighted1 := mul_lt_mul_of_pos_right first E.positive
  have weighted2 := mul_le_mul_of_nonneg_right second E.nonnegative
  have norm := norm_lt (18/25) (63/100) d t 1 E.unit (by norm_num) (by norm_num)
  nlinarith only [weighted1,weighted2,norm]

theorem second_source (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (cLow : 99/100<c) (sHigh : s<9/100) :
    (793/500)*c-s-(6/25)*(c*t+s*d)*t<1+c*d-s*t := by
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have tOne : t≤1 := le_trans E.ordered eb.2.1
  have first := mul_pos (sub_pos.mpr cLow) E.positive
  have second := mul_nonneg C.nonnegative (sub_nonneg.mpr tOne)
  have kLow : 603/1000<c*d-s*t := by nlinarith only [first,second,eb.1,sHigh]
  have rel := relative c s d t C E
  have correction := mul_nonneg rel.2 E.nonnegative
  linarith only [kLow,cb.2.1,C.nonnegative,correction]

theorem second_target (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (cLow : 99/100<c) (sHigh : s<9/100) :
    (793/500)*d+t+(c*t+s*d)*((13/50)*c-(43/500)*s)<
      1+(c*d-s*t)+(c*t+s*d) := by
  have cb := CommonCases.CanonicalScalars.bounds c s C.positive C.nonnegative C.ordered C.unit
  have cs := mul_nonneg C.positive.le C.nonnegative
  have short := mul_nonneg C.nonnegative (show 0≤1-(13/50)*c by linarith only [cb.2.1])
  have first : 793/500-c-s+(13/50)*c*s-(43/500)*s^2<3/5 := by
    nlinarith only [cLow,short,sq_nonneg s]
  have second : 1+s-c+(13/50)*c^2-(43/500)*c*s<9/25 := by
    nlinarith only [cLow,sHigh,C.unit,sq_nonneg s,cs]
  have weighted1 := mul_lt_mul_of_pos_right first E.positive
  have weighted2 := mul_le_mul_of_nonneg_right second.le E.nonnegative
  have norm := norm_lt (3/5) (9/25) d t 1 E.unit (by norm_num) (by norm_num)
  nlinarith only [weighted1,weighted2,norm]

theorem third_source (c s d t : ℝ) (C : Frame c s) (E : Frame d t) :
    (19/25)*c-s-(6/25)*(c*t+s*d)*t<c*d-s*t := by
  have eb := CommonCases.CanonicalScalars.bounds d t E.positive E.nonnegative E.ordered E.unit
  have dSquare := mul_nonneg E.positive.le (sub_nonneg.mpr eb.2.1)
  have first : 0<d+(6/25)*t^2-19/25 := by nlinarith only [eb.1,dSquare,E.unit]
  have second : 0≤1-t+(6/25)*d*t := by
    nlinarith only [E.ordered,eb.2.1,mul_nonneg E.positive.le E.nonnegative]
  have weighted1 := mul_pos C.positive first
  have weighted2 := mul_nonneg C.nonnegative second
  nlinarith only [weighted1,weighted2]

theorem third_target (c s d t : ℝ) (C : Frame c s) (E : Frame d t)
    (cLow : 49/50<c) (sHigh : s<9/50) :
    (19/25)*d+t+(413/500)*(c*t+s*d)*s<1+c*t+s*d := by
  have factor : 0<1-(413/500)*s := by linarith only [sHigh]
  have product := mul_pos (sub_pos.mpr cLow) factor
  have coefficient : 83/100<c*(1-(413/500)*s) := by nlinarith only [product,sHigh]
  have weighted := mul_le_mul_of_nonneg_right coefficient.le E.nonnegative
  have extra := mul_nonneg (mul_nonneg C.nonnegative E.positive.le) factor.le
  have norm := norm_lt (19/25) (17/100) d t 1 E.unit (by norm_num) (by norm_num)
  nlinarith only [weighted,extra,norm]

end N12Compact.C1092MPPMNonpositivePredecessor
