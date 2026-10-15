import Compact.Geometry.CornerWallMarkerNegativeCorner
import Compact.Geometry.CornerWallMarkerNegativeBounds

noncomputable section

/-! Genuine-marker support reductions for negative L after its backward
U separator. The original strict L corner forces this larger-tilt range;
the two scalar margins are supplied separately. -/
namespace N12Compact.CornerWallMarkerNegativeLarge

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner

def X (c s : ℝ) : ℝ := s-1+(1-(457/500)*s)/c

def leftMargin (c s d t l r : ℝ) : ℝ :=
  l+r-1+l^2*X c s+l*r*(c+d-2-d^2)+
    r^2*(43/500+t*(1-d))

def wallMargin (c s d t l r : ℝ) : ℝ :=
  1-l+l*X c s+r*(c-3+(1-(457/500)*t)/d+l+r*t/d)

/-- The actual W marker and genuine top marker cap bound the support
when L's negative tilt is at least W's negative tilt. -/
theorem wall_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (order : t≤r) (marker : W.Inside (457/500) 2)
    (cap : W.loV+W.side≤(457/500)*t+3*W.c) :
    lower W r l≤(r*W.c-l*t)*((457/500)*W.c-2*t)+
      (r*t+l*W.c)*((457/500)*t+3*W.c-W.side) := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hd : 0<W.c := by linarith only [wb.1]
  have lc : 0≤l := by linarith only [lb.1]
  have cosine := cosine_order ln wn order
  have ep : 0≤r*W.c-l*t := by
    have first := mul_nonneg hd.le (sub_nonneg.mpr order)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,second]
  have kp : 0≤r*t+l*W.c :=
    add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc hd.le)
  have form : lower W r l=(r*W.c-l*t)*W.loU+(r*t+l*W.c)*W.loV := by
    rw [lower_in_bands]
    rw [ws]
    rw [show r*W.c+l*(-t)=r*W.c-l*t by ring,
      show -r*(-t)+l*W.c=r*t+l*W.c by ring]
    rw [abs_of_nonneg ep,abs_of_nonneg kp]
    ring
  have markerU := marker.1.le
  rw [ws] at markerU
  have first := mul_nonneg ep (sub_nonneg.mpr markerU)
  have second := mul_nonneg kp (sub_nonneg.mpr cap)
  rw [form]
  nlinarith only [first,second]

/-- Backward L-U followed by forward L-V, with both original marker
coefficients 457/500 retained. -/
theorem left_axis_of_margin (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (wCap : W.loV+W.side≤(457/500)*t+3*W.c)
    (leftOrder : t≤r) (wMarker : W.Inside (457/500) 2)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : L.loV+L.side≤lower W r L.c)
    (margin : 0≤leftMargin O.c O.s W.c t L.c r) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0<W.c := by linarith only [wb.1]
  let H := O.s*L.c+O.c*r
  let E := r*W.c-L.c*t
  let K := r*t+L.c*W.c
  let M := (457/500)*W.c-2*t
  let T := (457/500)*t+3*W.c
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have kp : 0≤K := add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc.le hd.le)
  have bottom := CornerWallMarkerNegativeCorner.bottom_support O L.c r
    (2*O.c+(457/500)*O.s) on ln oBox oCap
  rw [sameOL] at bottom
  have upper := wall_support W t L.c r wn ln ws leftOrder wMarker wCap
  rw [←sameLW] at upper
  have wall0 := FourSquareBLBridge.left_wall L lc.le lBox
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  rw [ls] at wall0
  have wall : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall0]
  have selectedBottom := mul_nonneg hc.le (sub_nonneg.mpr ol)
  have bottomWeighted := mul_nonneg lc.le (sub_nonneg.mpr bottom)
  have firstWeighted := mul_nonneg lc.le selectedBottom
  have wallWeighted := mul_nonneg hc.le wall
  have upperWeighted := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr upper)
  have secondWeighted := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr lw)
  let Q := O.c*(L.c+r)+L.c*(O.c*H+L.c)+O.c*r*K
  let R := L.c^2*(2*O.c+(457/500)*O.s)+O.c*r*(E*M+K*T)
  have qp : 0<Q := by
    have first := mul_pos hc (show 0<L.c+r by linarith only [lc,ln.1])
    have second := mul_nonneg lc.le (add_nonneg (mul_nonneg hc.le hp) lc.le)
    have third := mul_nonneg (mul_nonneg hc.le ln.1) kp
    dsimp [Q]; linarith only [first,second,third]
  have combined : L.side*Q≤R := by
    dsimp [Q,R,H,E,K,M,T]
    nlinarith only [bottomWeighted,firstWeighted,wallWeighted,upperWeighted,secondWeighted]
  have identity : Q-R=O.c*leftMargin O.c O.s W.c t L.c r := by
    calc
      _ = O.c*leftMargin O.c O.s W.c t L.c r+
          O.c*(1-(L.c^2+r^2))-
          O.c*(2*L.c*r+(457/500)*r^2)*(W.c^2+t^2-1) := by
        dsimp [Q,R,H,E,K,M,T,leftMargin,X]
        field_simp [ne_of_gt hc]
        <;> ring
      _ = _ := by rw [ln.2.2,wn.2.2]; ring
  have scaledMargin := mul_nonneg hc.le margin
  have strictWidth := mul_pos (sub_pos.mpr side) qp
  nlinarith only [combined,identity,scaledMargin,strictWidth]

/-- Backward L-U followed by forward W-V. The whole left square and
its real container wall supply the support term, with no virtual seed. -/
theorem wall_axis_of_margin (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (wCap : W.loV+W.side≤(457/500)*t+3*W.c)
    (leftOrder : t≤r)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : upper L t W.c≤W.loV)
    (margin : 0≤wallMargin O.c O.s W.c t L.c r) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0<W.c := by linarith only [wb.1]
  let H := O.s*L.c+O.c*r
  let K := r*t+L.c*W.c
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have kp : 0≤K := add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc.le hd.le)
  have cosine := cosine_order ln wn leftOrder
  have pp : t*L.c-W.c*r≤0 := by
    have first := mul_nonneg hd.le (sub_nonneg.mpr leftOrder)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,second]
  have form : upper L t W.c=(t*L.c-W.c*r)*L.loU+K*(L.loV+L.side) := by
    rw [upper_in_bands]
    rw [ls]
    rw [show t*L.c+W.c*(-r)=t*L.c-W.c*r by ring,
      show -t*(-r)+W.c*L.c=K by dsimp [K]; ring]
    rw [abs_of_nonpos pp,abs_of_nonneg kp]
    ring
  have wall0 := FourSquareBLBridge.left_wall L lc.le lBox
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  rw [ls] at wall0
  have wall : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall0]
  have supportIdentity :
      r*upper L t W.c+W.c*L.loU-L.side*r*K=
        K*(L.c*L.loU+r*L.loV) := by
    rw [form]
    dsimp [K]
    linear_combination -W.c*L.loU*ln.2.2
  have support : 0≤r*upper L t W.c+W.c*L.loU-L.side*r*K := by
    rw [supportIdentity]
    exact mul_nonneg kp wall
  have bottom := CornerWallMarkerNegativeCorner.bottom_support O L.c r
    (2*O.c+(457/500)*O.s) on ln oBox oCap
  rw [sameOL] at bottom
  have selectedBottom := mul_nonneg hc.le (sub_nonneg.mpr ol)
  have bottomWeighted := mul_nonneg hd.le (sub_nonneg.mpr bottom)
  have firstWeighted := mul_nonneg hd.le selectedBottom
  have supportWeighted := mul_nonneg hc.le support
  have selectedWall := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr lw)
  have cap := wCap
  rw [←sameLW] at cap
  have capWeighted := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr cap)
  let Q := W.c*(O.c*H+L.c+O.c)+O.c*r*K+O.c*r
  let R := W.c*L.c*(2*O.c+(457/500)*O.s)+O.c*r*((457/500)*t+3*W.c)
  have qp : 0<Q := by
    have first := mul_pos hd (show 0<O.c*H+L.c+O.c by
      linarith only [mul_nonneg hc.le hp,lc,hc])
    have second := mul_nonneg (mul_nonneg hc.le ln.1) kp
    have third := mul_nonneg hc.le ln.1
    dsimp [Q]; linarith only [first,second,third]
  have combined : L.side*Q≤R := by
    dsimp [Q,R,H,K]
    nlinarith only [bottomWeighted,firstWeighted,supportWeighted,selectedWall,capWeighted]
  have identity : Q-R=O.c*W.c*wallMargin O.c O.s W.c t L.c r := by
    dsimp [Q,R,H,K,wallMargin,X]
    field_simp [ne_of_gt hc,ne_of_gt hd]
    <;> ring
  have scaledMargin := mul_nonneg (mul_nonneg hc.le hd.le) margin
  have strictWidth := mul_pos (sub_pos.mpr side) qp
  nlinarith only [combined,identity,scaledMargin,strictWidth]

/-- The complete backward L-U / forward L-V selector. The actual L
corner derives the stronger tilt restriction before the scalar is applied. -/
theorem left_axis (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (wCap : W.loV+W.side≤(457/500)*t+3*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (corner : L.Inside 1 1) (wMarker : W.Inside (457/500) 2)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : L.loV+L.side≤lower W r L.c) : False := by
  have cosine := cosine_order wn on order
  have restricted := CornerWallMarkerNegativeCorner.restrictions O L r on ln ls
    side sameOL oBox oCap corner ol (le_trans wide cosine) (le_trans order small)
  have leftOrder : t≤r := le_trans small restricted.2.le
  apply left_axis_of_margin O L W r t on ln wn ls ws side sameOL sameLW
    oBox lBox oCap wCap leftOrder wMarker ol lw
  simpa only [leftMargin,X,CornerWallMarkerNegativeBounds.X, mul_comm, mul_left_comm,
    mul_assoc] using CornerWallMarkerNegativeBounds.left_margin on wn ln order
      small wide restricted.1.le leftOrder

/-- The complete backward L-U / forward W-V selector with the same
original corner restriction and genuine marker caps. -/
theorem wall_axis (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (wCap : W.loV+W.side≤(457/500)*t+3*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (corner : L.Inside 1 1)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : upper L t W.c≤W.loV) : False := by
  have cosine := cosine_order wn on order
  have restricted := CornerWallMarkerNegativeCorner.restrictions O L r on ln ls
    side sameOL oBox oCap corner ol (le_trans wide cosine) (le_trans order small)
  have leftOrder : t≤r := le_trans small restricted.2.le
  apply wall_axis_of_margin O L W r t on ln wn ls side sameOL sameLW
    oBox lBox oCap wCap leftOrder ol lw
  simpa only [wallMargin,X,CornerWallMarkerNegativeBounds.X] using
    CornerWallMarkerNegativeBounds.wall_margin on wn ln order small wide
      restricted.1.le restricted.2.le

#print axioms left_axis_of_margin
#print axioms wall_axis_of_margin
#print axioms left_axis
#print axioms wall_axis
end N12Compact.CornerWallMarkerNegativeLarge
