import Compact.Geometry.CornerWallMarkerMixedBounds
import Compact.Geometry.CornerWallNegativeMixed
import Compact.Geometry.CornerWallMarkerLongitudinal
import Compact.Geometry.CornerWallMarkerNegativeHighBounds

/-! The genuine-marker negative-L O-v / L-v selector on the full
canonical arc. The smaller L angle range reuses the positive-L disk;
the larger range follows a finite-difference arc certificate. Both real
foreign-marker caps and all side corrections are retained.
Source only, uncompiled. -/
namespace N12Compact.CornerWallMarkerNegativeMixed

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
open CornerWallMarkerMixedBounds

theorem low_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : r≤t) (small : t≤3/5) (wide : 4/5≤d) :
    0≤1+(l/c)*boundary c s+l*(s*l+c*r)/c+l/d-(r*d-l*t)-
      (l/d)*(t+3*d) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have dc := cosine_order wn on order
  have dl := cosine_order wn ln leftOrder
  have cp : 0<c := by linarith only [wide,dc]
  have dp : 0<d := by linarith only [wide]
  have lp : 0<l := by linarith only [lb.1]
  let H := c*(1+l)*(l+1-2*d)-s*l*r
  have hp : 0≤H := by
    rcases le_total r s with low | high
    · have cl := cosine_order on ln low
      have first := mul_nonneg (mul_nonneg cp.le
        (show 0≤1+l by linarith only [lp])) (sub_nonneg.mpr dc)
      have second := mul_nonneg (mul_nonneg on.1 lp.le) (sub_nonneg.mpr low)
      have third := mul_nonneg (sub_nonneg.mpr cl)
        (show 0≤c*l+2*c-1 by
          have product := mul_nonneg cp.le lp.le
          linarith only [wide,dc,product])
      have identity : H=2*c*(1+l)*(c-d)+s*l*(s-r)+
          (l-c)*(c*l+2*c-1) := by
        dsimp [H]
        linear_combination -l*on.2.2
      nlinarith only [identity,first,second,third]
    · have lc := cosine_order ln on high
      have first := mul_nonneg cp.le (sub_nonneg.mpr high)
      have second := mul_nonneg on.1 (sub_nonneg.mpr lc)
      have cross : 0≤c*r-s*l := by nlinarith only [first,second]
      have crossWeighted := mul_nonneg ln.1 cross
      have gap := mul_nonneg (mul_nonneg cp.le
        (show 0≤1+l by linarith only [lp])) (sub_nonneg.mpr dl)
      have identity : H=2*c*(1+l)*(l-d)+r*(c*r-s*l) := by
        dsimp [H]
        linear_combination -c*ln.2.2
      nlinarith only [identity,crossWeighted,gap]
  have multiplied := mul_nonneg ln.1 hp
  have correctionIdentity :
      c*(1+l)*((s/c)*l*(l-1)+r*(l+1-2*d))=r*H := by
    calc
      _ = r*H+s*l*(l^2+r^2-1) := by
        dsimp [H]
        field_simp [ne_of_gt cp]
        <;> ring
      _ = _ := by rw [ln.2.2]; ring
  have correction : 0≤(s/c)*l*(l-1)+r*(l+1-2*d) := by
    have scaled : 0≤c*(1+l)*((s/c)*l*(l-1)+r*(l+1-2*d)) := by
      nlinarith only [correctionIdentity,multiplied]
    exact nonneg_of_mul_nonneg_right scaled
      (mul_pos cp (show 0<1+l by linarith only [lp]))
  have disk := linear_margin on wn ln order small wide
  have identity :
      (1+(l/c)*boundary c s+l*(s*l+c*r)/c+l/d-(r*d-l*t)-
        (l/d)*(t+3*d))-(1+l*(G c s+t+(1-t)/d-3)-r*(1-d)) =
      (s/c)*l*(l-1)+r*(l+1-2*d) := by
    dsimp [G]
    field_simp [ne_of_gt cp,ne_of_gt dp]
    <;> ring
  nlinarith only [disk,identity,correction]

theorem wall_support (W : OpenSquare) (t l r H : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (order : r≤t) (box : InsideContainer W) (cap : W.loV+W.side≤H) :
    W.c*lower W r l≤l*H-W.side*(l-W.c*(r*W.c-l*t)) := by
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
    dsimp [K]
    exact add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc hd.le)
  have form : lower W r l=E*(W.loU+W.side)+K*W.loV := by
    rw [lower_negative_nonpos W t r l ws ep kp]
    dsimp [E,K]; ring
  have wall0 := FourSquareBLBridge.left_wall W hd.le box
  rw [ws,abs_neg,abs_of_nonneg wn.1] at wall0
  dsimp [centerX] at wall0
  rw [ws] at wall0
  have wall : 0≤W.c*W.loU+t*W.loV := by nlinarith only [wall0]
  have wallWeighted := mul_nonneg (neg_nonneg.mpr ep) wall
  have capWeighted := mul_nonneg lc (sub_nonneg.mpr cap)
  have identity :
      W.c*lower W r l-(l*H-W.side*(l-W.c*E)) =
        E*(W.c*W.loU+t*W.loV)+l*(W.loV+W.side-H) := by
    rw [form]
    dsimp [E,K]
    linear_combination l*W.loV*wn.2.2
  dsimp [E] at identity
  nlinarith only [identity,wallWeighted,capWeighted]

theorem low_sector (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+3*W.c)
    (order : O.s≤t) (leftOrder : r≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W r L.c) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0<W.c := by linarith only [wide]
  let H := O.s*L.c+O.c*r
  let E := r*W.c-L.c*t
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have incoming := CornerWallNegativeMixed.singleton_lower O L r on ln ls lBox ol
  change L.c*(O.loV+O.side)+L.side*L.c*H≤O.c*L.loV at incoming
  have cosine := cosine_order wn ln leftOrder
  have en : E≤0 := by
    have first := mul_nonneg hd.le (sub_nonneg.mpr leftOrder)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    dsimp [E]; nlinarith only [first,second]
  have wall := wall_support W t L.c r (t+3*W.c) wn ln ws leftOrder wBox top
  rw [←same] at wall
  have selected := mul_nonneg hd.le (sub_nonneg.mpr lw)
  have first := mul_nonneg hd.le (sub_nonneg.mpr incoming)
  have second := mul_nonneg hc.le (sub_nonneg.mpr wall)
  have third := mul_nonneg hc.le selected
  let Q := O.c*W.c+W.c*L.c*H+O.c*(L.c-W.c*E)
  have qp : 0<Q := by
    have p0 := mul_pos hc hd
    have p1 := mul_nonneg (mul_nonneg hd.le lc.le) hp
    have p2 := mul_nonneg hc.le
      (show 0≤L.c-W.c*E by nlinarith only [mul_nonneg hd.le (neg_nonneg.mpr en),lc])
    dsimp [Q]; linarith only [p0,p1,p2]
  have combined : W.c*L.c*(O.loV+O.side)+L.side*Q≤O.c*L.c*(t+3*W.c) := by
    dsimp [Q,E]
    nlinarith only [first,second,third]
  have scalar := low_margin on wn ln order leftOrder small wide
  have identity :
      (O.c*W.c)*(1+(L.c/O.c)*boundary O.c O.s+L.c*H/O.c+
        L.c/W.c-E-(L.c/W.c)*(t+3*W.c))=
      W.c*L.c*boundary O.c O.s+Q-O.c*L.c*(t+3*W.c) := by
    dsimp [Q]
    field_simp [ne_of_gt hc,ne_of_gt hd]
    <;> ring
  have scalarScaled := mul_nonneg (mul_nonneg hc.le hd.le) scalar
  have width := mul_pos (sub_pos.mpr side) qp
  have face := mul_pos (mul_pos hd lc) (sub_pos.mpr bottomFace)
  dsimp [H,E] at identity
  nlinarith only [combined,identity,scalarScaled,width,face]

/-- Above W's tilt, the genuine NW and top marker caps bound both
low faces visible in L's V direction. The complete side correction is
kept; no point at height 2.88 is used. -/
theorem high_wall_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (order : t≤r)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c) :
    lower W r l+(W.side-1)*CornerWallMarkerLongitudinal.H W.c t r l≤
      r*CornerWallMarkerLongitudinal.Y W.c t+
        l*CornerWallMarkerLongitudinal.X W.c t := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hd : 0≤W.c := by linarith only [wb.1]
  have lc : 0≤l := by linarith only [lb.1]
  let E := r*W.c-l*t
  let K := r*t+l*W.c
  have cosine := cosine_order ln wn order
  have ep : 0≤E := by
    have first := mul_nonneg hd (sub_nonneg.mpr order)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    dsimp [E]; nlinarith only [first,second]
  have kp : 0≤K := add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc hd)
  have form : lower W r l=E*W.loU+K*W.loV := by
    rw [lower_negative_pos W t r l ws ep kp]
  have first := mul_nonneg ep (sub_nonneg.mpr northwest)
  have second := mul_nonneg kp (sub_nonneg.mpr top)
  have identity :
      E*((33/20)*W.c-(47/20)*t-1)+K*((457/500)*t+3*W.c-1)=
        r*CornerWallMarkerLongitudinal.Y W.c t+
          l*CornerWallMarkerLongitudinal.X W.c t := by
    dsimp [E,K,CornerWallMarkerLongitudinal.X,CornerWallMarkerLongitudinal.Y]
    linear_combination ((33/20)*r+3*l)*wn.2.2
  have sum : CornerWallMarkerLongitudinal.H W.c t r l=E+K := by
    dsimp [CornerWallMarkerLongitudinal.H,E,K]; ring
  rw [sum]
  nlinarith only [form,first,second,identity]

/-- The high-tilt mixed selector, with its scalar obligation stated in
exactly the form produced by the two real marker faces. -/
theorem high_sector_of_margin (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c)
    (leftOrder : t≤r)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W r L.c)
    (margin : 0≤1+(L.c/O.c)*boundary O.c O.s+
      (L.c/O.c)*(O.s*L.c+O.c*r)-
      r*CornerWallMarkerLongitudinal.Y W.c t-
      L.c*CornerWallMarkerLongitudinal.X W.c t) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0≤W.c := by linarith only [wb.1]
  let H := O.s*L.c+O.c*r
  let h := CornerWallMarkerLongitudinal.H W.c t r L.c
  let Q := O.c+L.c*H+O.c*h
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have cosine := cosine_order ln wn leftOrder
  have ep : 0≤r*W.c-L.c*t := by
    have first := mul_nonneg hd (sub_nonneg.mpr leftOrder)
    have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,second]
  have kp : 0≤r*t+L.c*W.c :=
    add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc.le hd)
  have hnonnegative : 0≤h := by
    dsimp [h,CornerWallMarkerLongitudinal.H]
    linarith only [ep,kp]
  have qp : 0<Q := by
    have first := mul_nonneg lc.le hp
    have second := mul_nonneg hc.le hnonnegative
    dsimp [Q]; linarith only [hc,first,second]
  have incoming := CornerWallNegativeMixed.singleton_lower O L r on ln ls lBox ol
  have high := high_wall_support W t L.c r wn ln ws leftOrder northwest top
  rw [←same] at high
  have selected := mul_nonneg hc.le (sub_nonneg.mpr lw)
  have upper := mul_nonneg hc.le (sub_nonneg.mpr high)
  have combined : L.c*(O.loV+O.side)+L.side*Q≤
      O.c*(r*CornerWallMarkerLongitudinal.Y W.c t+
        L.c*CornerWallMarkerLongitudinal.X W.c t+h) := by
    dsimp [Q,H,h]
    nlinarith only [incoming,selected,upper]
  have identity :
      O.c*(1+(L.c/O.c)*boundary O.c O.s+(L.c/O.c)*H-
        r*CornerWallMarkerLongitudinal.Y W.c t-
        L.c*CornerWallMarkerLongitudinal.X W.c t)=
      L.c*boundary O.c O.s+Q-
        O.c*(r*CornerWallMarkerLongitudinal.Y W.c t+
          L.c*CornerWallMarkerLongitudinal.X W.c t+h) := by
    dsimp [Q]
    field_simp [ne_of_gt hc]
    <;> ring
  have scaled := mul_nonneg hc.le margin
  have face := mul_pos lc (sub_pos.mpr bottomFace)
  have width := mul_pos (sub_pos.mpr side) qp
  dsimp [H] at identity
  nlinarith only [combined,identity,scaled,face,width]

/-- The complete negative-L mixed selector, with only genuine marker
faces and the stated exterior angle order. -/
theorem sector (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (bottomFace : boundary O.c O.s<O.loV+O.side)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c)
    (order : O.s≤t) (small : t≤3/5) (wide : 4/5≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W r L.c) : False := by
  rcases le_total r t with low | high
  · have looseTop : W.loV+W.side≤t+3*W.c := by
      linarith only [top,wn.1]
    exact low_sector O L W r t on ln wn ls ws side same lBox wBox
      bottomFace looseTop order low small wide ol lw
  · apply high_sector_of_margin O L W r t on ln wn ls ws side same
      lBox bottomFace northwest top high ol lw
    exact CornerWallMarkerNegativeHighBounds.margin on wn ln order high small wide

#print axioms sector
end N12Compact.CornerWallMarkerNegativeMixed
