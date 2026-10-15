import Compact.Geometry.CornerWallSharedAxis
import Compact.Geometry.CornerWallNegativeMargin

/-! Exact support reduction for a negative left singleton. The independent
continuous scalar margin closes the range where L tilts no farther than W.
The reduction uses all three actual container walls and both full sides;
it cannot be obtained by replacing a singleton with its seed segment. -/
namespace N12Compact.CornerWallNegativeShared

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner

/-- The original bottom wall and upper U face bound the bottom square's
lower support on a negative singleton's U axis. -/
theorem bottom_support (O : OpenSquare) (l r : ℝ)
    (on : Normal O.c O.s) (ln : Normal l r)
    (box : InsideContainer O) (cap : O.loU+O.side≤2*O.c+O.s) :
    O.c*lower O l (-r)≤l*(2*O.c+O.s)-
      O.side*(O.c*(O.s*l+O.c*r)+l) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0≤l := by linarith only [lb.1]
  let P := O.c*l-O.s*r
  let H := O.s*l+O.c*r
  have pp : 0≤P := by
    have first := mul_nonneg hc.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr on.2.1)
    dsimp [P]; nlinarith only [first,second]
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg on.1 lc) (mul_nonneg hc.le ln.1)
  have form : lower O l (-r)=P*O.loU-H*(O.loV+O.side) := by
    rw [lower_in_bands]
    rw [show l*O.c+(-r)*O.s=P by dsimp [P]; ring,
      show -l*O.s+(-r)*O.c=-H by dsimp [H]; ring]
    rw [abs_of_nonneg pp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  have wall0 := ThreeSquare.bottom_wall O hc.le box
  rw [abs_of_nonneg on.1] at wall0
  dsimp [centerY] at wall0
  have wall : 0≤O.s*O.loU+O.c*O.loV := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg hp wall
  have capWeighted := mul_nonneg lc (sub_nonneg.mpr cap)
  have identity :
      O.c*lower O l (-r)-
        (l*(2*O.c+O.s)-O.side*(O.c*H+l)) =
      -H*(O.s*O.loU+O.c*O.loV)+l*(O.loU+O.side-(2*O.c+O.s)) := by
    rw [form]
    dsimp [P,H]
    linear_combination l*O.loU*on.2.2
  dsimp [H] at identity
  nlinarith only [identity,wallWeighted,capWeighted]

/-- If negative L tilts no farther than negative W, W's real left wall
and the foreign top seed bound its lower support on L's V axis. -/
theorem wall_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (order : r≤t) (box : InsideContainer W)
    (cap : W.loV+W.side≤t+(72/25)*W.c) :
    W.c*lower W r l≤l*(t+(72/25)*W.c)-
      W.side*(l-W.c*(r*W.c-l*t)) := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hd : 0<W.c := by linarith only [wb.1]
  have lc : 0≤l := by linarith only [lb.1]
  let E := r*W.c-l*t
  let K := r*t+l*W.c
  have cosine := cosine_order wn ln order
  have ep : E≤0 := by
    have first := mul_nonneg hd.le (sub_nonneg.mpr order)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    dsimp [E]; nlinarith only [first,second]
  have kp : 0≤K := by
    dsimp [K]; exact add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc hd.le)
  have form : lower W r l=E*(W.loU+W.side)+K*W.loV := by
    have raw := lower_negative_nonpos W t r l ws
      (show r*W.c-l*t≤0 from ep)
      (show 0≤r*t+l*W.c from kp)
    rw [raw]; dsimp [E,K]; ring
  have wall0 := FourSquareBLBridge.left_wall W hd.le box
  rw [ws,abs_neg,abs_of_nonneg wn.1] at wall0
  dsimp [centerX] at wall0
  rw [ws] at wall0
  have wall : 0≤W.c*W.loU+t*W.loV := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg (neg_nonneg.mpr ep) wall
  have capWeighted := mul_nonneg lc (sub_nonneg.mpr cap)
  have identity :
      W.c*lower W r l-(l*(t+(72/25)*W.c)-W.side*(l-W.c*E)) =
        E*(W.c*W.loU+t*W.loV)+l*(W.loV+W.side-(t+(72/25)*W.c)) := by
    rw [form]
    dsimp [E,K]
    linear_combination l*W.loV*wn.2.2
  dsimp [E] at identity
  nlinarith only [identity,wallWeighted,capWeighted]

/-- The full selected negative-L sector reduces exactly to the displayed
continuous scalar margin. The margin is a premise here, not a claimed
consequence of unverified finite data. -/
theorem sector_of_margin (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L) (wBox : InsideContainer W)
    (oCap : O.loU+O.side≤2*O.c+O.s)
    (wCap : W.loV+W.side≤t+(72/25)*W.c) (leftOrder : r≤t)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : L.loV+L.side≤lower W r L.c)
    (margin : 0≤L.c+r-W.c+
      L.c*r*(O.c+t-72/25+(1-t)/W.c)+
      L.c^2*(O.s+W.c-2+(1-O.s)/O.c)) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0<W.c := by linarith only [wb.1]
  let H := O.s*L.c+O.c*r
  let E := r*W.c-L.c*t
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have ep : E≤0 := by
    have cosine := cosine_order wn ln leftOrder
    have first := mul_nonneg hd.le (sub_nonneg.mpr leftOrder)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    dsimp [E]; nlinarith only [first,second]
  have bottom := bottom_support O L.c r on ln oBox oCap
  rw [sameOL] at bottom
  have upper := wall_support W t L.c r wn ln ws leftOrder wBox wCap
  rw [←sameLW] at upper
  have wall0 := FourSquareBLBridge.left_wall L lc.le lBox
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  rw [ls] at wall0
  have wall : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall0]
  have selectedBottom := mul_nonneg hc.le (sub_nonneg.mpr ol)
  have selectedWall := mul_nonneg hd.le (sub_nonneg.mpr lw)
  have bottomWeighted := mul_nonneg (mul_nonneg hd.le lc.le) (sub_nonneg.mpr bottom)
  have firstWeighted := mul_nonneg (mul_nonneg hd.le lc.le) selectedBottom
  have wallWeighted := mul_nonneg (mul_nonneg hc.le hd.le) wall
  have upperWeighted := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr upper)
  have secondWeighted := mul_nonneg (mul_nonneg hc.le ln.1) selectedWall
  let Q := W.c*O.c*(L.c+r)+W.c*L.c*(O.c*H+L.c)+O.c*r*(L.c-W.c*E)
  let R := W.c*L.c^2*(2*O.c+O.s)+O.c*r*L.c*(t+(72/25)*W.c)
  have qp : 0<Q := by
    have first := mul_pos (mul_pos hd hc) (show 0<L.c+r by linarith only [lc,ln.1])
    have second := mul_nonneg (mul_nonneg hd.le lc.le)
      (add_nonneg (mul_nonneg hc.le hp) lc.le)
    have third := mul_nonneg (mul_nonneg hc.le ln.1)
      (show 0≤L.c-W.c*E by nlinarith only [mul_nonneg hd.le (neg_nonneg.mpr ep),lc])
    dsimp [Q]; linarith only [first,second,third]
  have combined : L.side*Q≤R := by
    dsimp [Q,R,H,E]
    nlinarith only [bottomWeighted,firstWeighted,wallWeighted,upperWeighted,secondWeighted]
  have identity :
      Q-R=O.c*W.c*(L.c+r-W.c+
        L.c*r*(O.c+t-72/25+(1-t)/W.c)+
        L.c^2*(O.s+W.c-2+(1-O.s)/O.c)) := by
    calc
      _ = O.c*W.c*(L.c+r-W.c+
          L.c*r*(O.c+t-72/25+(1-t)/W.c)+
          L.c^2*(O.s+W.c-2+(1-O.s)/O.c))+
          O.c*W.c^2*(1-(L.c^2+r^2)) := by
        dsimp [Q,R,H,E]
        field_simp [ne_of_gt hc,ne_of_gt hd]
        <;> ring
      _ = _ := by rw [ln.2.2]; ring
  have scaledMargin := mul_nonneg (mul_nonneg hc.le hd.le) margin
  have strictWidth := mul_pos (sub_pos.mpr side) qp
  nlinarith only [combined,identity,scaledMargin,strictWidth]

/-- The negative L-U / L-V selector is impossible when L tilts no farther
than W. The two actual foreign wall seeds enter through the top cap and
the stronger wall tilt range. -/
theorem sector (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L) (wBox : InsideContainer W)
    (oCap : O.loU+O.side≤2*O.c+O.s)
    (wCap : W.loV+W.side≤t+(72/25)*W.c)
    (order : O.s≤t) (leftOrder : r≤t)
    (small : t≤51/100) (wide : 43/50≤W.c)
    (ol : L.loU+L.side≤lower O L.c (-r))
    (lw : L.loV+L.side≤lower W r L.c) : False := by
  exact sector_of_margin O L W r t on ln wn ls ws side sameOL sameLW
    oBox lBox wBox oCap wCap leftOrder ol lw
    (CornerWallNegativeMargin.margin on wn ln order leftOrder small wide)

end N12Compact.CornerWallNegativeShared
