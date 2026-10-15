import Compact.Geometry.CornerWallNegativeShared

/-! The actual bottom marker makes the backward negative-left separator
much narrower. Its corner forces the bottom cosine below .914 and the
left sine above .6. No wall-square assumption is needed. -/
namespace N12Compact.CornerWallMarkerNegativeCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner

theorem bottom_support (O : OpenSquare) (l r H : ℝ)
    (on : Normal O.c O.s) (ln : Normal l r)
    (box : InsideContainer O) (cap : O.loU+O.side≤H) :
    O.c*lower O l (-r)≤l*H-O.side*(O.c*(O.s*l+O.c*r)+l) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0≤l := by linarith only [lb.1]
  let P := O.c*l-O.s*r
  let K := O.s*l+O.c*r
  have pp : 0≤P := by
    have first := mul_nonneg hc.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr on.2.1)
    dsimp [P]; nlinarith only [first,second]
  have kp : 0≤K := by
    dsimp [K]; exact add_nonneg (mul_nonneg on.1 lc) (mul_nonneg hc.le ln.1)
  have form : lower O l (-r)=P*O.loU-K*(O.loV+O.side) := by
    rw [lower_in_bands]
    rw [show l*O.c+(-r)*O.s=P by dsimp [P]; ring,
      show -l*O.s+(-r)*O.c=-K by dsimp [K]; ring]
    rw [abs_of_nonneg pp,abs_of_nonpos (neg_nonpos.mpr kp)]
    ring
  have wall0 := ThreeSquare.bottom_wall O hc.le box
  rw [abs_of_nonneg on.1] at wall0
  dsimp [centerY] at wall0
  have wall : 0≤O.s*O.loU+O.c*O.loV := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg kp wall
  have capWeighted := mul_nonneg lc (sub_nonneg.mpr cap)
  have identity :
      O.c*lower O l (-r)-(l*H-O.side*(O.c*K+l))=
        -K*(O.s*O.loU+O.c*O.loV)+l*(O.loU+O.side-H) := by
    rw [form]
    dsimp [P,K]
    linear_combination l*O.loU*on.2.2
  dsimp [K] at identity
  nlinarith only [identity,wallWeighted,capWeighted]

theorem restrictions (O L : OpenSquare) (r : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (ls : L.s=-r)
    (side : 1<L.side) (same : O.side=L.side)
    (box : InsideContainer O)
    (cap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (corner : L.Inside 1 1)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (wide : 4/5≤O.c) (small : O.s≤3/5) :
    O.c<457/500 ∧ 3/5<r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have cp : 0<O.c := by linarith only [wide]
  have lp : 0<L.c := by linarith only [lb.1]
  have cornerU : L.c-r<L.loU+L.side := by
    have h := corner.2.1
    rw [ls] at h
    nlinarith only [h]
  have support := bottom_support O L.c r (2*O.c+(457/500)*O.s) on ln box cap
  rw [same] at support
  have owned := mul_pos cp (sub_pos.mpr cornerU)
  have selected := mul_nonneg cp.le (sub_nonneg.mpr ol)
  have factor : 0<O.c*(O.s*L.c+O.c*r)+L.c := by
    have first := mul_nonneg on.1 lp.le
    have second := mul_nonneg cp.le ln.1
    have third := mul_nonneg cp.le (add_nonneg first second)
    linarith only [third,lp]
  have width := mul_pos (sub_pos.mpr side) factor
  have identity :
      L.c*(2*O.c+(457/500)*O.s)-(O.c*(O.s*L.c+O.c*r)+L.c)-
        O.c*(L.c-r)=
      L.c*((O.c-1)+O.s*(457/500-O.c))+O.c*r*(1-O.c) := by ring
  have necessary : 0<L.c*((O.c-1)+O.s*(457/500-O.c))+O.c*r*(1-O.c) := by
    nlinarith only [support,owned,selected,width,identity]
  have cSmall : O.c<457/500 := by
    by_contra no
    have first := mul_nonneg (mul_nonneg cp.le (sub_nonneg.mpr ob.2.1))
      (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg on.1 (show 0≤O.c-457/500 by linarith only [no])
    have third := mul_nonneg lp.le (sq_nonneg (1-O.c))
    have fourth := mul_nonneg lp.le second
    nlinarith only [necessary,first,third,fourth]
  have slope : (3/4)*L.c<r := by
    by_contra no
    have first := mul_nonneg (mul_nonneg cp.le (sub_nonneg.mpr ob.2.1))
      (show 0≤(3/4)*L.c-r by linarith only [no])
    have replacement := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤457/500-O.c by linarith only [cSmall])
    have factor := mul_nonneg (sub_nonneg.mpr wide)
      (show 0≤(3/4)*O.c-11/20 by linarith only [wide])
    have polynomial :
        (1-O.c)*(1-(3/4)*O.c)+(3/5)*(O.c-457/500)=
          29/2500+(O.c-4/5)*((3/4)*O.c-11/20) := by ring
    have scalar : 0<(1-O.c)*(1-(3/4)*O.c)+O.s*(O.c-457/500) := by
      nlinarith only [replacement,factor,polynomial]
    have weighted := mul_pos lp scalar
    nlinarith only [necessary,first,weighted]
  have rLarge : 3/5<r := by
    by_contra no
    have rSmall : r≤3/5 := le_of_not_gt no
    have lr : (3/4)*L.c+r>0 := by linarith only [lp,ln.1]
    have squared := mul_pos (sub_pos.mpr slope) lr
    have bounded := mul_nonneg (sub_nonneg.mpr rSmall)
      (show 0≤3/5+r by linarith only [ln.1])
    nlinarith only [squared,bounded,ln.2.2]
  exact ⟨cSmall,rLarge⟩

#print axioms restrictions
end N12Compact.CornerWallMarkerNegativeCorner
