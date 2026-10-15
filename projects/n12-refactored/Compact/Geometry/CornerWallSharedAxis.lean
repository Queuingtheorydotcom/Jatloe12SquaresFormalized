import Compact.Geometry.CornerWallSharedMargin
import Compact.Geometry.CornerWallCycle

/-! The other common transverse axis for positive L. Actual O bottom
containment and W left containment give support bounds whose coefficient
vector is strictly inside the unit disk. No center enclosure is used. -/
namespace N12Compact.CornerWallSharedAxis

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner

/-- A lower support bound for the real bottom square on any positive
singleton's transverse axis. Both its actual width and bottom wall enter. -/
theorem bottom_support (O : OpenSquare) (l r : ℝ)
    (on : Normal O.c O.s) (lp : 0≤l) (rp : 0≤r)
    (side : 0<O.side) (box : InsideContainer O)
    (cap : O.loU+O.side≤2*O.c+O.s) :
    O.side*(O.c*(O.c*l+O.s*r)+r)-r*(2*O.c+O.s)≤
      O.c*upper O (-r) l := by
  have ob := normal_bounds on
  have hc : 0<O.c := by linarith only [ob.1]
  let D := -r*O.c+l*O.s
  let K := r*O.s+l*O.c
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg rp on.1) (mul_nonneg lp hc.le)
  have absBound : 0≤D+|D| := by linarith only [neg_le_abs D]
  have radius := mul_nonneg side.le absBound
  have support : D*O.loU+K*(O.loV+O.side)≤upper O (-r) l := by
    have formula := upper_in_bands O (-r) l
    have u : (-r)*O.c+l*O.s=D := by rfl
    have v : -(-r)*O.s+l*O.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg kp] at formula
    nlinarith only [formula,radius]
  have wall0 := ThreeSquare.bottom_wall O hc.le box
  rw [abs_of_nonneg on.1] at wall0
  dsimp [centerY] at wall0
  have wall : 0≤O.s*O.loU+O.c*O.loV := by nlinarith only [wall0]
  have wp := mul_nonneg kp wall
  have cp := mul_nonneg rp (sub_nonneg.mpr cap)
  have sp := mul_nonneg hc.le (sub_nonneg.mpr support)
  have identity :
      O.c*(D*O.loU+K*(O.loV+O.side)) =
        K*(O.s*O.loU+O.c*O.loV)-r*O.loU+O.side*O.c*K := by
    dsimp [D,K]
    linear_combination -r*O.loU*O.unit_normal
  dsimp [K] at identity wp
  nlinarith only [identity,wp,cp,sp]

/-- An upper bound on the real wall square's lower support. The improved
top seed supplies the height 72/25, while actual left containment couples
both faces. -/
theorem wall_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (box : InsideContainer W) (top : W.loV+W.side≤t+(72/25)*W.c) :
    W.c*lower W (-r) l≤
      l*(t+(72/25)*W.c)-W.side*(W.c*(r*W.c+l*t)+l) := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have wc : 0<W.c := by linarith only [wb.1]
  have lc : 0≤l := by linarith only [lb.1]
  let h := r*W.c+l*t
  let k := l*W.c-r*t
  have hp : 0≤h := by
    dsimp [h]; exact add_nonneg (mul_nonneg ln.1 wc.le) (mul_nonneg lc wn.1)
  have kp : 0≤k := by
    have first := mul_nonneg wc.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]; nlinarith only [first,second]
  have form : lower W (-r) l=-h*(W.loU+W.side)+k*W.loV := by
    have raw := lower_negative_nonpos W t (-r) l ws
      (show (-r)*W.c-l*t≤0 by dsimp [h] at hp; linarith only [hp])
      (show 0≤(-r)*t+l*W.c by dsimp [k] at kp; linarith only [kp])
    rw [raw]
    dsimp [h,k]; ring
  have wall0 := FourSquareBLBridge.left_wall W wc.le box
  rw [ws,abs_neg,abs_of_nonneg wn.1] at wall0
  dsimp [centerX] at wall0
  rw [ws] at wall0
  have wall : 0≤W.c*(W.loU+W.side)+t*(W.loV+W.side)-W.side*(W.c+t) := by
    nlinarith only [wall0]
  have wp := mul_nonneg hp wall
  have tp := mul_nonneg lc (sub_nonneg.mpr top)
  have identity :
      W.c*lower W (-r) l-
        (l*(t+(72/25)*W.c)-W.side*(W.c*h+l)) =
      -h*(W.c*(W.loU+W.side)+t*(W.loV+W.side)-W.side*(W.c+t))+
        l*(W.loV+W.side-(t+(72/25)*W.c)) := by
    rw [form]
    dsimp [h,k]
    linear_combination l*W.loV*wn.2.2
  dsimp [h] at identity
  nlinarith only [identity,wp,tp]

/-- The O/L and L/W separators cannot both use positive L's transverse
axis when W tilts at least as far as O. The original top-owner seed is
retained through the exact top-face bound. -/
theorem sector (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (wBox : InsideContainer W)
    (oCap : O.loU+O.side≤2*O.c+O.s)
    (wCap : W.loV+W.side≤t+(72/25)*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : upper O (-L.s) L.c≤L.loV)
    (lw : L.loV+L.side≤lower W (-L.s) L.c) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have hd : 0<W.c := by linarith only [wide]
  have lc : 0≤L.c := by linarith only [lb.1]
  have oside : 0<O.side := by rw [sameOL]; linarith only [side]
  have first := bottom_support O L.c L.s on lc ln.1 oside oBox oCap
  have second := wall_support W t L.c L.s wn ln ws wBox wCap
  rw [sameOL] at first
  rw [←sameLW] at second
  have selected : upper O (-L.s) L.c+L.side≤lower W (-L.s) L.c := by
    linarith only [ol,lw]
  have selectedWeighted := mul_nonneg (mul_nonneg hc.le hd.le) (sub_nonneg.mpr selected)
  have firstWeighted := mul_nonneg hd.le (sub_nonneg.mpr first)
  have secondWeighted := mul_nonneg hc.le (sub_nonneg.mpr second)
  let Q := O.c*L.c+L.s*(O.s+1/O.c)+1+L.s*W.c+L.c*t+L.c/W.c
  let R := L.s*(2+O.s/O.c)+(72/25)*L.c+L.c*t/W.c
  have qp : 0<Q := by
    have p0 := mul_nonneg hc.le lc
    have p1 := mul_nonneg ln.1 (add_nonneg on.1 (div_nonneg zero_le_one hc.le))
    have p2 := mul_nonneg ln.1 hd.le
    have p3 := mul_nonneg lc wn.1
    have p4 := div_nonneg lc hd.le
    dsimp [Q]
    linarith only [p0,p1,p2,p3,p4]
  have required : L.side*Q≤R := by
    have identity :
        (O.c*W.c)*(L.side*Q-R) =
        W.c*(L.side*(O.c*(O.c*L.c+O.s*L.s)+L.s)-L.s*(2*O.c+O.s))+
          O.c*W.c*L.side-
          O.c*(L.c*(t+(72/25)*W.c)-L.side*(W.c*(L.s*W.c+L.c*t)+L.c)) := by
      dsimp [Q,R]
      field_simp [ne_of_gt hc,ne_of_gt hd]
      <;> ring
    have weighted : (O.c*W.c)*(L.side*Q-R)≤0 := by
      nlinarith only [identity,firstWeighted,secondWeighted,selectedWeighted]
    have unscaled := nonpos_of_mul_nonpos_right weighted (mul_pos hc hd)
    linarith only [unscaled]
  have scalar := CornerWallSharedMargin.shared_axis on wn ln order small wide
  have identity :
      Q-R=1+L.c*(O.c+t-72/25+(1-t)/W.c)+
        L.s*(O.s+W.c-2+(1-O.s)/O.c) := by
    dsimp [Q,R]
    field_simp [ne_of_gt hc,ne_of_gt hd]
    <;> ring
  have width := mul_pos (sub_pos.mpr side) qp
  nlinarith only [required,scalar,identity,width]

end N12Compact.CornerWallSharedAxis
