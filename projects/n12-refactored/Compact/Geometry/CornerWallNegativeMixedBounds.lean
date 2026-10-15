import Compact.Geometry.CornerWallCycleBounds

/-! Uniform continuous margins for the negative-L O-v / L-v selector.
The only ranges are the ordering of L and W; no finite pose intervals
are used. The high-L remainder has a direct positive-square certificate. -/
namespace N12Compact.CornerWallNegativeMixedBounds
open C977CornerCubic C977CornerSectorBounds CornerWallCycleBounds

/-- The incoming bottom face loses less than one tenth under the
canonical projection on the stronger original wall range. -/
theorem baseline {c s : ℝ} (on : Normal c s)
    (small : s≤51/100) (wide : 43/50≤c) :
    9/10≤(bottom c s+s)/c := by
  have ob := normal_bounds on
  have hc : 0<c := by linarith only [wide]
  have c1 : 0<1+c := by linarith only [hc]
  have interval := mul_nonneg on.1 (sub_nonneg.mpr small)
  have factor : 0≤2499/10000+(49/100)*s-s^2 := by
    nlinarith only [interval,small]
  have product := mul_nonneg (sub_nonneg.mpr small) factor
  have cubic : s^2*(1-s)≤13/100 := by
    have identity :
        127449/1000000-s^2*(1-s)=
          (51/100-s)*(2499/10000+(49/100)*s-s^2) := by ring
    nlinarith only [product,identity]
  have cosineSquare := mul_nonneg (sub_nonneg.mpr wide)
    (show 0≤c+43/50 by linarith only [hc])
  have cosineCube := mul_nonneg (sub_nonneg.mpr wide) (sq_nonneg c)
  have polynomial : 0≤(1/10)*c^2*(1+c)-s^2*(1-s) := by
    nlinarith only [cubic,cosineSquare,cosineCube]
  have identity :
      (1+c)*((1/10)*c^2-(1-c)*(1-s))=
        (1/10)*c^2*(1+c)-s^2*(1-s) := by
    linear_combination (1-s)*on.2.2
  have weighted : 0≤(1+c)*((1/10)*c^2-(1-c)*(1-s)) := by
    linarith only [identity,polynomial]
  have defect := nonneg_of_mul_nonneg_right weighted c1
  have ratioIdentity :
      c^2*((bottom c s+s)/c-9/10)=
        (1/10)*c^2-(1-c)*(1-s) := by
    calc
      _ = (1/10)*c^2-(1-c)*(1-s)-(c^2+s^2-1) := by
        unfold bottom
        field_simp [ne_of_gt hc]
        <;> ring
      _ = _ := by rw [on.2.2]; ring
  have scaled : 0≤c^2*((bottom c s+s)/c-9/10) := by
    linarith only [ratioIdentity,defect]
  have h := nonneg_of_mul_nonneg_right scaled (pow_pos hc 2)
  linarith only [h]

private theorem projection_bound {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t)
    (small : t≤51/100) (wideC : 43/50≤c) (wideD : 43/50≤d) :
    (bottom c s+2*s)/c+t+(1-t)/d≤72/25 := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have hc : 0<c := by linarith only [wideC]
  have hd : 0<d := by linarith only [wideD]
  have square := mul_nonneg (sub_nonneg.mpr wideC)
    (show 0≤c+43/50 by linarith only [hc])
  have first : 1/c≤50/43 := by
    apply (div_le_iff₀ hc).mpr
    linarith only [wideC]
  have quarter : s*(1-s)≤1/4 := by nlinarith only [sq_nonneg (s-1/2)]
  have second : s*(1-s)/c^2≤625/1849 := by
    apply (div_le_iff₀ (pow_pos hc 2)).mpr
    nlinarith only [quarter,square]
  have identity : (bottom c s+2*s)/c=1/c+s*(1-s)/c^2 := by
    unfold bottom
    field_simp [ne_of_gt hc]
    <;> ring
  have denominator := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
  have third : t+(1-t)/d≤50/43 := by
    have identity : d*(t+(1-t)/d)=1-t*(1-d) := by
      field_simp [ne_of_gt hd]
      <;> ring
    have scaled : d*(t+(1-t)/d-50/43)≤0 := by
      nlinarith only [identity,denominator,wideD]
    have h := nonpos_of_mul_nonpos_right scaled hd
    linarith only [h]
  linarith only [identity,first,second,third]

/-- When L tilts no farther than W, the scalar response is minimized
at the horizontal singleton. Its remaining margin is at least 1/50. -/
theorem low_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : r≤t)
    (small : t≤51/100) (wide : 43/50≤d) :
    0<1+(l/c)*bottom c s+l*(s*l+c*r)/c+
      l/d-(r*d-l*t)-(l/d)*(t+(72/25)*d) := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have hd : 0<d := by linarith only [wide]
  have dc := cosine_order wn on order
  have dl := cosine_order wn ln leftOrder
  have core := baseline on (le_trans order small) (le_trans wide dc)
  have coefficient := projection_bound on wn small (le_trans wide dc) wide
  let alpha := bottom c s/c+t+(1-t)/d-72/25
  let beta := s/c
  have betaPos : 0≤beta := div_nonneg on.1 hc.le
  have incoming : 0≤ -alpha-2*beta := by
    dsimp [alpha,beta]
    have identity : (bottom c s+2*s)/c=bottom c s/c+2*(s/c) := by ring
    linarith only [coefficient,identity]
  have correction := mul_nonneg betaPos (sub_nonneg.mpr lb.2.1)
  have first := mul_nonneg (sub_nonneg.mpr lb.2.1)
    (show 0≤ -alpha-beta*(1+l) by nlinarith only [incoming,correction])
  have second := mul_nonneg ln.1 (sub_nonneg.mpr dl)
  have endpoint : 1/50≤1+alpha+beta := by
    have product := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (show 0≤1-t by linarith only [small])
    have identity : d*(t+(1-t)/d-1)=(1-d)*(1-t) := by
      field_simp [ne_of_gt hd]
      <;> ring
    have scaled : 0≤d*(t+(1-t)/d-1) := by linarith only [identity,product]
    have h := nonneg_of_mul_nonneg_right scaled hd
    have coreIdentity : (bottom c s+s)/c=bottom c s/c+s/c := by ring
    dsimp [alpha,beta]
    linarith only [h,core,coreIdentity]
  have identity :
      (1+(l/c)*bottom c s+l*(s*l+c*r)/c+
        l/d-(r*d-l*t)-(l/d)*(t+(72/25)*d))-(1+alpha+beta)=
        (1-l)*(-alpha-beta*(1+l))+r*(l-d) := by
    dsimp [alpha,beta]
    field_simp [ne_of_gt hc,ne_of_gt hd]
    <;> ring
  nlinarith only [identity,first,second,endpoint]

private theorem wall_coefficients {d t : ℝ} (wn : Normal d t)
    (small : t≤51/100) (wide : 43/50≤d) :
    2*t^2+(43/500)*d*t+(72/25)*d^2-d≤19/10 ∧
      (457/500)*d^2+t^2+(22/25)*d*t-t≤457/500 := by
  have wb := normal_bounds wn
  have cosine := mul_nonneg (sub_nonneg.mpr wide) (sub_nonneg.mpr wb.2.1)
  have defect : 1-d≤(27/50)*t^2 := by
    nlinarith only [cosine,wn.2.2,sq_nonneg t]
  have dot := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
  have square := sq_nonneg (t-13/100)
  have first : 2*t^2+(43/500)*d*t+(72/25)*d^2-d≤19/10 := by
    nlinarith only [defect,dot,square,wn.2.2,wn.1]
  have tilt := mul_nonneg wn.1 (sub_nonneg.mpr small)
  have second : (457/500)*d^2+t^2+(22/25)*d*t-t≤457/500 := by
    nlinarith only [dot,tilt,wn.2.2,wn.1]
  exact ⟨first,second⟩

private theorem remaining_square {l r : ℝ} (ln : Normal l r) :
    0≤(1-l)*(1-(3/5)*l)+r*(l-457/500) := by
  have lb := normal_bounds ln
  by_cases high : 457/500≤l
  · have first := mul_nonneg (sub_nonneg.mpr lb.2.1)
      (show 0≤1-(3/5)*l by linarith only [lb.2.1])
    have second := mul_nonneg ln.1 (sub_nonneg.mpr high)
    exact add_nonneg first second
  · have low : l≤457/500 := (lt_of_not_ge high).le
    have sine : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
    have product := mul_nonneg (sub_nonneg.mpr sine) (sub_nonneg.mpr low)
    have identity :
        (1-l)*(1-(3/5)*l)-(5/7)*(457/500-l)=
          (3/5)*(l-3/4)^2+l/70+27/2800 := by ring
    nlinarith only [identity,product,sq_nonneg (l-3/4),lb.1]

/-- The high-L support uses W's actual marker rather than an assumed
virtual vertical wall. A fixed positive-square remainder closes it. -/
theorem high_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤51/100) (wide : 43/50≤d) :
    0≤1+(l/c)*bottom c s+l*(s*l+c*r)/c+(r*t+l*d)-
      (r*d-l*t)*((457/500)*d-2*t)-(r*t+l*d)*(t+(72/25)*d) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have lp : 0≤l := by linarith only [lb.1]
  have dc := cosine_order wn on order
  have wideC := le_trans wide dc
  have core := baseline on (le_trans order small) wideC
  have slope : s/c≤3/5 := by
    apply (div_le_iff₀ hc).mpr
    linarith only [order,small,wideC]
  have first := mul_nonneg lp (sub_nonneg.mpr core)
  have second := mul_nonneg (mul_nonneg lp (sub_nonneg.mpr lb.2.1))
    (sub_nonneg.mpr slope)
  have incoming : (3/10)*l+(3/5)*l^2≤(l/c)*bottom c s+(s/c)*l^2 := by
    have identity :
        (l/c)*bottom c s+(s/c)*l^2-
          ((3/10)*l+(3/5)*l^2)=
        l*((bottom c s+s)/c-9/10)+l*(1-l)*(3/5-s/c) := by
      field_simp [ne_of_gt hc]
      <;> ring
    nlinarith only [identity,first,second]
  have bounds := wall_coefficients wn small wide
  have x := mul_nonneg lp (sub_nonneg.mpr bounds.1)
  have y := mul_nonneg ln.1 (sub_nonneg.mpr bounds.2)
  have remainder := remaining_square ln
  have identity :
      1+(l/c)*bottom c s+l*(s*l+c*r)/c+(r*t+l*d)-
        (r*d-l*t)*((457/500)*d-2*t)-(r*t+l*d)*(t+(72/25)*d)=
      1+(l/c)*bottom c s+(s/c)*l^2+l*r-
        l*(2*t^2+(43/500)*d*t+(72/25)*d^2-d)-
        r*((457/500)*d^2+t^2+(22/25)*d*t-t) := by
    field_simp [ne_of_gt hc]
    <;> ring
  nlinarith only [identity,incoming,x,y,remainder]

end N12Compact.CornerWallNegativeMixedBounds
