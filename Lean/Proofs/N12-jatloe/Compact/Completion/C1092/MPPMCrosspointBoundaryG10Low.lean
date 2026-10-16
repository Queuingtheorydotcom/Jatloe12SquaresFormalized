import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Clamp
import Compact.Completion.C1092.MPPMCrosspointBoundaryEndpoints
import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars
import Compact.Completion.CommonCases.UnitCircleChord

/-! BOUNDARY-SCALARS section 8.1. Finite circle chords replace both
derivative monotonicity arguments; the small remaining sector has a
rational coefficient-norm bound. All equal-angle endpoints are retained. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

theorem G10_upper_formula (c s d t h r : ℝ) (q : Quarter h r)
    (order : 0≤deltaE d t h r) :
    G10 c s d t h r=(1+h*r-2*h-r-FC c s h r)*d+
      (r^2-(36/25)*r)*t+r := by
  unfold G10
  rw [abs_of_nonneg order]
  dsimp [kE,deltaE,E0]
  linear_combination (d/2)*q.unit

theorem G10_lower_formula (c s d t h r : ℝ) (q : Quarter h r)
    (order : deltaE d t h r≤0) :
    G10 c s d t h r=(h*(h+r)-2*h-r-FC c s h r)*d+
      (r*(h+r-36/25))*t+r := by
  unfold G10
  rw [abs_of_nonpos order]
  dsimp [kE,deltaE,E0]
  linear_combination -(d/2)*q.unit

theorem low_quarter_bounds (h r : ℝ) (q : Quarter h r)
    (hh : 4/5≤h) (rr : r≤3/5) : Normal h r ∧ h≤1 ∧ 1≤h+r ∧ h+r≤7/5 := by
  have bn : Normal h r := ⟨q.sine,by linarith only [hh,rr],q.unit⟩
  have bounds := normal_bounds bn
  have fixed : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have dot := dot_le_one fixed bn
  exact ⟨bn,bounds.2.1,bounds.2.2.2.2.1,by nlinarith only [dot,rr]⟩

private theorem before (d t h r P Q : ℝ) (en : Normal d t) (bn : Normal h r)
    (order : t≤r) (negative : Q≤0) (endpoint : 0≤P*r-Q*h) :
    P*h+Q*r≤P*d+Q*t := by
  have eb := normal_bounds en
  have bb := normal_bounds bn
  by_cases pn : 0≤P
  · have cosine := cosine_order bn en order
    have first := mul_nonneg pn (sub_nonneg.mpr cosine)
    have last := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr order)
    nlinarith only [first,last]
  · have pn : P≤0 := (lt_of_not_ge pn).le
    have chord := CommonCases.UnitCircleChord.increasing
      (show 0<h by linarith only [bb.1]) (show 0≤d by linarith only [eb.1])
      bn.2.2 en.2.2 bn.1 en.1 order
      (neg_nonneg.mpr pn) (neg_nonneg.mpr negative)
      (show 0≤(-Q)*h-(-P)*r by nlinarith only [endpoint])
    nlinarith only [chord]

private theorem after (d t h r P Q : ℝ) (en : Normal d t) (bn : Normal h r)
    (order : r≤t) (pn : P≤0) (qn : Q≤0) (endpoint : 0≤Q*h-P*r) :
    P*h+Q*r≤P*d+Q*t := by
  have eb := normal_bounds en
  have bb := normal_bounds bn
  have chord := CommonCases.UnitCircleChord.decreasing
    (show 0<h by linarith only [bb.1]) (show 0≤d by linarith only [eb.1])
    bn.2.2 en.2.2 bn.1 en.1 order
    (neg_nonneg.mpr pn) (neg_nonneg.mpr qn)
    (show 0≤(-P)*r-(-Q)*h by nlinarith only [endpoint])
  nlinarith only [chord]

theorem G10_low_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r)
    (hh : 4/5≤h) (rr : r≤3/5) : 0≤G10 c s d t h r := by
  have qb := low_quarter_bounds h r q hh rr
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have cap := FC_low_cap c s h r cn steep q hh rr
  let F := -(3496/3125)*h+(11387/12500)*r
  have weighted := mul_le_mul_of_nonneg_right cap dp.le
  have aligned := lower_endpoint_D h r q hh rr
  by_cases order : 0≤deltaE d t h r
  · let P := 1+h*r-2*h-r-F
    let Q := r^2-(36/25)*r
    have formula := G10_upper_formula c s d t h r q order
    have bound : P*d+Q*t+r≤G10 c s d t h r := by
      dsimp [P,Q,F]
      nlinarith only [formula,weighted]
    have qn : Q≤0 := by
      have product := mul_nonpos_of_nonneg_of_nonpos q.sine
        (show r-36/25≤0 by linarith only [rr])
      dsimp [Q]; nlinarith only [product]
    have comparison : 0≤P-h*(r-36/25) := by
      dsimp [P,F]
      nlinarith only [hh,rr]
    have endpoint := mul_nonneg q.sine comparison
    have sine : t≤r := sine_order qb.1 en (by dsimp [deltaE] at order; nlinarith only [order])
    have chord := before d t h r P Q en qb.1 sine qn
      (by dsimp [Q]; nlinarith only [endpoint])
    have atEnd : P*h+Q*r+r=
        h+2*r-2+(3496/3125)*h^2-(1+11387/12500)*h*r+(14/25)*r^2 := by
      dsimp [P,Q,F]
      linear_combination (r-2)*q.unit
    linarith only [bound,chord,atEnd,aligned]
  · have order : deltaE d t h r≤0 := (lt_of_not_ge order).le
    let P := h*(h+r)-2*h-r-F
    let Q := r*(h+r-36/25)
    have formula := G10_lower_formula c s d t h r q order
    have bound : P*d+Q*t+r≤G10 c s d t h r := by
      dsimp [P,Q,F]
      nlinarith only [formula,weighted]
    have qn : Q≤0 := by
      exact mul_nonpos_of_nonneg_of_nonpos q.sine (by linarith only [qb.2.2.2])
    have ql : -(11/25)*r≤Q := by
      have product := mul_nonneg q.sine (show 0≤h+r-1 by linarith only [qb.2.2.1])
      dsimp [Q]; nlinarith only [product]
    by_cases pn : 0≤P
    · have first := mul_nonneg pn dp.le
      have last := mul_le_mul_of_nonneg_right ql en.1
      have capT := mul_nonneg q.sine (show 0≤1-t by linarith only [en.2.1,eb.2.1])
      nlinarith only [bound,first,last,capT,q.sine]
    · have pn : P≤0 := (lt_of_not_ge pn).le
      let B := -(1746/3125)*h+(23887/12500)*r
      by_cases positive : 0≤B
      · have endpoint := mul_nonneg q.sine positive
        have derivative : Q*h-P*r=r*B := by dsimp [P,Q,F,B]; ring
        have sine : r≤t := sine_order en qb.1 (by dsimp [deltaE] at order; exact order)
        have chord := after d t h r P Q en qb.1 sine pn qn
          (by nlinarith only [derivative,endpoint])
        have atEnd : P*h+Q*r+r=
            h+2*r-2+(3496/3125)*h^2-(1+11387/12500)*h*r+(14/25)*r^2 := by
          dsimp [P,Q,F]
          linear_combination (h+r-2)*q.unit
        linarith only [bound,chord,atEnd,aligned]
      · have negative : B<0 := lt_of_not_ge positive
        have ratio : r<(293/1000)*h := by dsimp [B] at negative; linarith only [negative,hh]
        have ratioSquare := mul_pos (show 0<(293/1000)*h-r by linarith only [ratio])
          (show 0<(293/1000)*h+r by linarith only [hh,q.sine])
        have cosine : 959/1000<h := by
          apply lt_of_not_ge
          intro no
          have square := mul_nonneg (show 0≤959/1000-h by linarith only [no])
            (show 0≤959/1000+h by linarith only [hh])
          nlinarith only [square,ratioSquare,q.unit]
        have first := mul_nonneg q.cosine (show 0≤h-959/1000 by linarith only [cosine])
        have last := mul_nonneg q.sine (show 0≤h-959/1000 by linarith only [cosine])
        have pl : -(7/10)*r≤P := by
          dsimp [P,F]
          nlinarith only [first,last,ratio,hh]
        have pWeight := mul_le_mul_of_nonneg_right pl dp.le
        have qWeight := mul_le_mul_of_nonneg_right ql en.1
        have norm := C1092MPPMNonpositivePredecessor.norm_le (7/10) (11/25) d t 1
          en.2.2 (by norm_num) (by norm_num)
        have weightedNorm := mul_nonneg q.sine (show 0≤1-(7/10)*d-(11/25)*t by linarith only [norm])
        nlinarith only [bound,pWeight,qWeight,weightedNorm]

end N12Compact.C1092MPPMCrosspointSupport
