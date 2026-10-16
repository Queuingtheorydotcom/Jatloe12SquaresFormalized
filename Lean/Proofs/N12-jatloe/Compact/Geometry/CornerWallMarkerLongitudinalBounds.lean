import Compact.Geometry.CornerWallMarkerLongitudinal

/-! Continuous positive-L longitudinal margins for the genuine top
marker and foreign NW marker. The whole wall sector is t≤3/5, d≥4/5.
The first margin reduces to one cubic; the second to a unit-circle sum. -/
namespace N12Compact.CornerWallMarkerLongitudinalBounds

open C977CornerCubic C977CornerSectorBounds CornerWallCycleBounds
open CornerWallMarkerLongitudinal

/-- The two coefficients retain their common wall normal. The chord of
d² on [4/5,1] bounds their sum; no angle enumeration is used. -/
theorem wall_bounds {d t : ℝ} (wn : Normal d t) (wide : 4/5≤d) :
    Y d t≤17/20 ∧ X d t+Y d t-d≤219/125 := by
  have wb := normal_bounds wn
  have hd : 0≤d := by linarith only [wide]
  have yproduct := mul_nonneg wn.1
    (show 0≤1-(13/20)*d by linarith only [wb.2.1])
  have ybound : Y d t≤17/20 := by
    dsimp [Y]
    nlinarith only [wide,yproduct,sq_nonneg t]
  have chord := mul_nonneg (sub_nonneg.mpr wide)
    (sub_nonneg.mpr wb.2.1)
  have cross := mul_nonneg hd wn.1
  have coupled : X d t+Y d t-d≤219/125 := by
    dsimp [X,Y]
    nlinarith only [wn.2.2,chord,cross,wide]
  exact ⟨ybound,coupled⟩

/-- One completed square certifies the cubic on the entire canonical
L sector. The rational center 3/5 is only an expansion point. -/
private theorem cubic_nonnegative {r : ℝ} (upper : r≤5/7) :
    0≤3/20-(341/500)*r+(41/40)*r^2-(1/2)*r^3 := by
  have correction := mul_nonneg (sq_nonneg (r-3/5))
    (show 0≤3/8-r/2 by linarith only [upper])
  have square := sq_nonneg ((1/10)*(r-3/5)+1/125)
  have identity :
      3/20-(341/500)*r+(41/40)*r^2-(1/2)*r^3 =
        9/5000+(1/125)*(r-3/5)+(r-3/5)^2*(17/40-r/2) := by ring
  nlinarith only [identity,correction,square]

/-- The bottom expression decreases with the allowed sine order. -/
private theorem bottom_bound {c s r t : ℝ} (on : Normal c s)
    (hr : 0≤r) (rupper : r≤1) (order : s≤t) (small : t≤3/5) :
    1-(1-r)*t-t^2≤(bottom c s+s*r)/c := by
  have ob := normal_bounds on
  have hc : 0<c := by linarith only [ob.1]
  have ssmall : s≤3/5 := le_trans order small
  have sine : s^2≤(3/5)*s := by
    nlinarith only [mul_nonneg on.1 (sub_nonneg.mpr ssmall)]
  have base : 0≤1-(1-r)*s-s^2 := by
    nlinarith only [sine,ssmall,mul_nonneg hr on.1]
  have inner : 1-(1-r)*s-s^2≤bottom c s+s*r := by
    have product := mul_nonneg
      (mul_nonneg on.1 (sub_nonneg.mpr ob.2.2.2.1))
      (sub_nonneg.mpr ob.2.1)
    have identity :
        c*((bottom c s+s*r)-(1-(1-r)*s-s^2))=
          s*(1-s)*(1-c) := by
      dsimp [bottom]
      field_simp [ne_of_gt hc]
      <;> ring
    have scaled : 0≤c*((bottom c s+s*r)-(1-(1-r)*s-s^2)) := by
      rw [identity]
      exact product
    have difference := nonneg_of_mul_nonneg_right scaled hc
    linarith only [difference]
  have numerator : 0≤bottom c s+s*r := le_trans base inner
  have division : bottom c s+s*r≤(bottom c s+s*r)/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [mul_nonneg numerator (sub_nonneg.mpr ob.2.1)]
  have ordered : 1-(1-r)*t-t^2≤1-(1-r)*s-s^2 := by
    have linear := mul_nonneg (sub_nonneg.mpr rupper) (sub_nonneg.mpr order)
    have square := mul_nonneg (sub_nonneg.mpr order)
      (show 0≤t+s by linarith only [on.1,order])
    nlinarith only [linear,square]
  exact le_trans ordered (le_trans inner division)

/-- The O-v / L-U margin with actual marker caps. -/
theorem bottom_axis {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d) :
    0≤1+(r/c)*bottom c s+(r/c)*(c*l+s*r)-l*Y d t-r*X d t := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have rsmall : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
  have wall := wall_bounds wn wide
  have base := bottom_bound on ln.1 lb.2.2.2.1 order small
  have first := mul_nonneg ln.1 (sub_nonneg.mpr base)
  have second := mul_nonneg (sub_nonneg.mpr ln.2.1)
    (sub_nonneg.mpr wall.1)
  have third := mul_nonneg ln.1 (sub_nonneg.mpr wall.2)
  have dupper : d≤1-t^2/2 := by
    nlinarith only [wn.2.2,sq_nonneg (d-1)]
  have fourth := mul_nonneg ln.1 (sub_nonneg.mpr dupper)
  have timeLinear := mul_nonneg
    (mul_nonneg ln.1 (sub_nonneg.mpr lb.2.2.2.1))
    (sub_nonneg.mpr small)
  have timeSquare := mul_nonneg ln.1
    (show 0≤(3/5)^2-t^2 by
      nlinarith only [mul_nonneg (sub_nonneg.mpr small)
        (show 0≤3/5+t by linarith only [wn.1])])
  have simplification :
      1+(r/c)*bottom c s+(r/c)*(c*l+s*r)-l*Y d t-r*X d t =
        1-l*Y d t+l*r+r*((bottom c s+s*r)/c-X d t) := by
    field_simp [ne_of_gt hc]
    <;> ring
  have lower : 1-(17/20)*l+l*r-(841/500)*r+(3/5)*r^2≤
      1+(r/c)*bottom c s+(r/c)*(c*l+s*r)-l*Y d t-r*X d t := by
    rw [simplification]
    nlinarith only [first,second,third,fourth,timeLinear,timeSquare]
  have lupper : l≤1-r^2/2 := by
    nlinarith only [ln.2.2,sq_nonneg (l-1)]
  have fifth := mul_nonneg
    (show 0≤17/20-r by linarith only [rsmall])
    (sub_nonneg.mpr lupper)
  have cubic := cubic_nonnegative rsmall
  nlinarith only [lower,fifth,cubic]

/-- The L-v / L-U margin. The actual O cap is stronger than the cap
used here, and no additional L-corner restriction is required. -/
theorem singleton_axis {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (wide : 4/5≤d) :
    0≤c*l+c*r+c*r*(c*l+s*r)+r^2-r^2*(2*c+s)-
      c*l*(l*Y d t+r*X d t) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<c := by linarith only [ob.1]
  have lc : 0≤l := by linarith only [lb.1]
  have wall := wall_bounds wn wide
  have ylow : 0≤1-Y d t := by linarith only [wall.1]
  have sum : 0≤l+r-1-(4/5)*l*r := by
    have product := mul_nonneg
      (show 0≤l+r-1 by linarith only [lb.2.2.2.2.1])
      (show 0≤3/2-(l+r) by linarith only [lb.2.2.2.2.2])
    nlinarith only [product,ln.2.2]
  have dotCorrection := mul_nonneg
    (mul_nonneg lc (sub_nonneg.mpr ln.2.1)) ylow
  have wallCorrection := mul_nonneg (mul_nonneg lc ln.1)
    (show 0≤9/5-(X d t+Y d t-d) by linarith only [wall.2])
  have base : 0≤l+r-l^2*Y d t+l*r*(d-X d t)-r^2 := by
    nlinarith only [sum,dotCorrection,wallCorrection,ln.2.2]
  have cosine := cosine_order wn on order
  have angleCorrection := mul_nonneg (mul_nonneg lc ln.1)
    (sub_nonneg.mpr cosine)
  let J := s+(1-s)/c-2
  have jidentity : c*(J+1)=(1-s)*(1-c) := by
    dsimp [J]
    field_simp [ne_of_gt hc]
    <;> ring
  have jnonnegative : 0≤c*(J+1) := by
    rw [jidentity]
    exact mul_nonneg (sub_nonneg.mpr ob.2.2.2.1)
      (sub_nonneg.mpr ob.2.1)
  have jlower := nonneg_of_mul_nonneg_right jnonnegative hc
  have last := mul_nonneg (sq_nonneg r) jlower
  have reduced : 0≤l+r-l^2*Y d t+l*r*(c-X d t)+r^2*J := by
    nlinarith only [base,angleCorrection,last]
  have identity :
      c*l+c*r+c*r*(c*l+s*r)+r^2-r^2*(2*c+s)-
        c*l*(l*Y d t+r*X d t) =
      c*(l+r-l^2*Y d t+l*r*(c-X d t)+r^2*J) := by
    dsimp [J]
    field_simp [ne_of_gt hc]
    <;> ring
  rw [identity]
  exact mul_nonneg hc.le reduced

#print axioms bottom_axis
#print axioms singleton_axis
end N12Compact.CornerWallMarkerLongitudinalBounds
