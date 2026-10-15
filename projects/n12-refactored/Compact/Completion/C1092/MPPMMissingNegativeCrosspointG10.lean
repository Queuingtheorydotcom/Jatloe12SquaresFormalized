import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG10Scalars

/-! MISSING-NEGATIVE-WALL-SCALARS §4, all boundary orientations. The
first range avoids the A-sign split by bounding its possible positive
part uniformly. Two exact quartics replace the remaining derivative
arguments. The full epsilon loss leaves the uniform margin 1/250. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic G10Scalars
set_option Elab.async false
noncomputable section

private theorem before_of_lower (d t h r : ℝ) (en : Normal d t)
    (q : Quarter h r) (order : r≤h) : deltaE d t h r≤0 := by
  have first := mul_nonneg en.1 (sub_nonneg.mpr order)
  have last := mul_nonneg q.cosine (sub_nonneg.mpr en.2.1)
  dsimp [deltaE]
  nlinarith only [first,last]

private theorem low (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r) (low : r≤3/5) :
    3/50≤G10 c s d t h r := by
  have qb := quarter_bounds q
  have lb := low_bounds q low
  have eb := recipient_bounds en large
  have cap := C1092MPPMNegativeCrosspointSupport.FC_low_cap c s h r cn steep q lb.1 low
  have capWeight := mul_le_mul_of_nonneg_left cap en.1
  have formula := before_formula c s d t h r q (before_of_lower d t h r en q lb.2.1)
  let A := h*(h+r)-(21/25)*h-(47/25)*r
  let B := r*(h+r-36/25)
  have comparison : t*A+d*B+r≤G10 c s d t h r := by
    dsimp [A,B]
    nlinarith only [capWeight,formula]
  have first := mul_nonneg (sub_nonneg.mpr qb.1)
    (show 0≤h+4/25 by linarith only [q.cosine])
  have last := mul_nonneg q.sine (show 0≤47/25-h by linarith only [qb.1])
  have Acap : A≤4/25 := by dsimp [A]; nlinarith only [first,last]
  have Bn : B≤0 := mul_nonpos_of_nonneg_of_nonpos q.sine
    (by linarith only [lb.2.2])
  have tWeight := mul_nonneg (show 0≤3/4-t by linarith only [eb.2.2])
    (show 0≤4/25-A by linarith only [Acap])
  have tCompare : (3/4)*A-3/250≤t*A := by nlinarith only [tWeight,eb.2.1]
  have dWeight := mul_nonneg (show 0≤3/4-d by linarith only [eb.1]) (neg_nonneg.mpr Bn)
  have dCompare : (3/4)*B≤d*B := by nlinarith only [dWeight]
  have identity : (3/4)*A+(3/4)*B+r=
      3/4-(63/100)*h-(149/100)*r+(3/2)*h*r := by
    dsimp [A,B]
    linear_combination (3/4)*q.unit
  have radial := low_radial q low
  linarith only [comparison,tCompare,dCompare,identity,radial]

private theorem middle (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (middle : 3/5≤r) (order : r≤h) : 47/1000≤G10 c s d t h r := by
  have bn : Normal h r := ⟨q.sine,order,q.unit⟩
  have cap := C1092MPPMNegativeCrosspointSupport.FC_middle_cap c s h r cn steep bn middle
  have weight := mul_le_mul_of_nonneg_left cap en.1
  have kc : kC h r h r=1 := by dsimp [kC]; nlinarith only [q.unit]
  have dc : deltaC h r h r=0 := by dsimp [deltaC]; ring
  have identity : G10 c s d t h r-G00 h r d t h r=t*((r-1)-FC c s h r) := by
    unfold G10 G00 width C1092MPPMNegativeCrosspointSupport.width
    rw [kc,dc,abs_zero]
    dsimp [kE,ell,C0]
    ring
  have base := G00_lower bn en middle large q
  nlinarith only [base,identity,weight]

private theorem high_before (c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r) (order : h≤r)
    (branch : deltaE d t h r≤0) : 3/50≤G10 c s d t h r := by
  have rn : Normal r h := ⟨q.cosine,order,by nlinarith only [q.unit]⟩
  have rb := normal_bounds rn
  have qb := quarter_bounds q
  have eb := recipient_bounds en large
  have sine : t≤h := C977CornerSectorBounds.sine_order rn en
    (by dsimp [deltaE] at branch; nlinarith only [branch])
  have sum : 141/100≤h+r := by
    have bound := large_sum rn (le_trans large sine)
    linarith only [bound]
  have cap := C1092MPPMNegativeCrosspointSupport.FC_high_cap c s h r cn q order
  have weight := mul_le_mul_of_nonneg_left cap en.1
  have formula := before_formula c s d t h r q branch
  let A := h*(h+r-3/2)-(109/100)*r
  let B := r*(h+r-36/25)
  have comparison : t*A+d*B+r≤G10 c s d t h r := by
    dsimp [A,B]
    nlinarith only [weight,formula]
  have An : A≤0 := by
    have product := mul_nonpos_of_nonneg_of_nonpos q.cosine
      (show h+r-3/2≤0 by linarith only [qb.2.2.2])
    dsimp [A]
    nlinarith only [product,q.sine]
  have Bn : B≤0 := mul_nonpos_of_nonneg_of_nonpos q.sine
    (by linarith only [qb.2.2.2])
  have tWeight := mul_nonneg (show 0≤3/4-t by linarith only [eb.2.2]) (neg_nonneg.mpr An)
  have dWeight := mul_nonneg (show 0≤3/4-d by linarith only [eb.1]) (neg_nonneg.mpr Bn)
  have first := mul_nonneg q.cosine (show 0≤h+r-141/100 by linarith only [sum])
  have last := mul_nonneg q.sine (show 0≤h+r-141/100 by linarith only [sum])
  have bound : (4/25)*r-(27/400)*h≤(3/4)*A+(3/4)*B+r := by
    dsimp [A,B]
    nlinarith only [first,last]
  nlinarith only [comparison,tWeight,dWeight,bound,order,rb.1]

private theorem high_after (c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r) (order : h≤r)
    (branch : 0≤deltaE d t h r) : 3/50≤G10 c s d t h r := by
  have qb := quarter_bounds q
  have eb := recipient_bounds en large
  have cap := C1092MPPMNegativeCrosspointSupport.FC_high_cap c s h r cn q order
  have weight := mul_le_mul_of_nonneg_left cap en.1
  have formula := after_formula c s d t h r q branch
  let A := 1+h*r-(3/2)*h-(109/100)*r
  let B := r*(r-36/25)
  have comparison : t*A+d*B+r≤G10 c s d t h r := by
    dsimp [A,B]
    nlinarith only [weight,formula]
  have halfWeight := mul_nonneg q.cosine
    (show 0≤1+r-2*h by linarith only [qb.1,order])
  have halfIdentity : (1+r)*(h-2*(1-r))=h*(1+r-2*h) := by
    linear_combination 2*q.unit
  have half : 2*(1-r)≤h := by
    have weighted : 0≤(1+r)*(h-2*(1-r)) := by rw [halfIdentity]; exact halfWeight
    have result := nonneg_of_mul_nonneg_right weighted (show 0<1+r by linarith only [q.sine])
    linarith only [result]
  have hr := mul_le_mul_of_nonneg_left qb.2.1 q.cosine
  have An : A≤0 := by dsimp [A]; nlinarith only [half,hr,q.sine]
  have Bn : B≤0 := mul_nonpos_of_nonneg_of_nonpos q.sine (by linarith only [qb.2.1])
  have tWeight := mul_nonneg (show 0≤3/4-t by linarith only [eb.2.2]) (neg_nonneg.mpr An)
  have dWeight := mul_nonneg (show 0≤3/4-d by linarith only [eb.1]) (neg_nonneg.mpr Bn)
  have identity : (3/4)*A+(3/4)*B+r=
      3/4+(3/4)*h*r-(9/8)*h+(3/4)*r^2-(359/400)*r := by dsimp [A,B]; ring
  have radial := high_radial q order
  nlinarith only [comparison,tWeight,dWeight,identity,radial]

theorem G10_lower (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r) :
    47/1000≤G10 c s d t h r := by
  by_cases lower : r≤3/5
  · have result := low c s d t h r cn steep en large q lower
    linarith only [result]
  by_cases order : r≤h
  · exact middle c s d t h r cn steep en large q (lt_of_not_ge lower).le order
  have order : h≤r := (lt_of_not_ge order).le
  by_cases branch : 0≤deltaE d t h r
  · have result := high_after c s d t h r cn en large q order branch
    linarith only [result]
  · have result := high_before c s d t h r cn en large q order (lt_of_not_ge branch).le
    linarith only [result]

/-- The allowance is only bounded above. Its sign need not be assumed:
the multiplier s*t*kC is nonnegative on the whole closed domain. -/
theorem G10star_lower (epsilon c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) : 1/250≤G10star epsilon c s d t h r := by
  have lower := G10_lower c s d t h r cn steep en large q
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0≤d := by linarith only [eb.1]
  have kn : 0≤kC c s h r := add_nonneg (mul_nonneg cp q.cosine) (mul_nonneg cn.1 q.sine)
  have kh : kC c s h r≤1 := by
    dsimp [kC]
    nlinarith only [cn.2.2,q.unit,sq_nonneg (c-h),sq_nonneg (s-r)]
  have squareC := mul_nonneg (sub_nonneg.mpr cn.2.1) (add_nonneg cp cn.1)
  have squareE := mul_nonneg (sub_nonneg.mpr en.2.1) (add_nonneg dp en.1)
  have st : 0≤s*t := mul_nonneg cn.1 en.1
  have stcap : s*t≤1/2 := by
    nlinarith only [squareC,squareE,cn.2.2,en.2.2,sq_nonneg (s-t)]
  have product := mul_le_mul_of_nonneg_right stcap kn
  have productcap : s*t*kC c s h r≤1/2 := by nlinarith only [product,kh]
  have loss := mul_le_mul_of_nonneg_right allowance (mul_nonneg st kn)
  dsimp [G10star]
  nlinarith only [lower,loss,productcap]

#print axioms G10star_lower
end
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
