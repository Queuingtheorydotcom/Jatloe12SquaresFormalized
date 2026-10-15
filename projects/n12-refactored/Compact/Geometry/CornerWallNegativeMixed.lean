import Compact.Geometry.CornerWallNegativeMixedBounds
import Compact.Geometry.CornerWallNegativeShared

/-! The negative singleton's O-v / L-v selector is excluded throughout
its canonical arc. Its actual left wall, full side and selected support
are retained. The high-angle wall comparison uses the actual W marker,
not an unproved upper U cap. -/
namespace N12Compact.CornerWallNegativeMixed

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner CornerWallCycleBounds

/-- Actual containment of negative L turns the O-v separator into a
lower bound on L's complete lower V face. -/
theorem singleton_lower (O L : OpenSquare) (r : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (ls : L.s=-r)
    (box : InsideContainer L)
    (ol : O.loV+O.side≤lower L (-O.s) O.c) :
    L.c*(O.loV+O.side)+L.side*L.c*(O.s*L.c+O.c*r)≤O.c*L.loV := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0≤O.c := by linarith only [ob.1]
  have lc : 0≤L.c := by linarith only [lb.1]
  let H := O.s*L.c+O.c*r
  let K := O.c*L.c-O.s*r
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc) (mul_nonneg hc ln.1)
  have kp : 0≤K := by
    have first := mul_nonneg hc (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,second]
  have form : lower L (-O.s) O.c=-H*(L.loU+L.side)+K*L.loV := by
    rw [lower_negative_nonpos L r (-O.s) O.c ls
      (by dsimp [H] at hp; linarith only [hp])
      (by dsimp [K] at kp; linarith only [kp])]
    dsimp [H,K]; ring
  have wall0 := FourSquareBLBridge.left_wall L lc box
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  rw [ls] at wall0
  have wall : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall0]
  have first := mul_nonneg hp wall
  have second := mul_nonneg lc (sub_nonneg.mpr ol)
  have identity :
      O.c*L.loV-L.c*(O.loV+O.side)-L.side*L.c*H =
        H*(L.c*L.loU+r*L.loV)+L.c*(lower L (-O.s) O.c-(O.loV+O.side)) := by
    rw [form]
    dsimp [H,K]
    linear_combination -O.c*L.loV*ln.2.2
  dsimp [H] at identity
  nlinarith only [identity,first,second]

/-- For L tilted farther than W, its V axis sees W's actual U-low/V-low
corner. The original wall marker bounds that U face directly. -/
theorem marker_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (order : t≤r) (marker : W.Inside (457/500) 2)
    (top : W.loV+W.side≤t+(72/25)*W.c) :
    lower W r l+W.side*(r*t+l*W.c)≤
      (r*W.c-l*t)*((457/500)*W.c-2*t)+(r*t+l*W.c)*(t+(72/25)*W.c) := by
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
  have owned := (negative_bands W t _ _ ws).mp marker
  have first := mul_nonneg ep (sub_nonneg.mpr owned.1.le)
  have second := mul_nonneg kp (sub_nonneg.mpr top)
  dsimp [E,K] at form first second
  nlinarith only [form,first,second]

/-- The O-v / L-v selector for negative L is impossible for every
canonical L angle on the stronger original wall range. -/
theorem sector (O L W : OpenSquare) (r t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (wn : Normal W.c t)
    (ls : L.s=-r) (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (wMarker : W.Inside (457/500) 2)
    (bottomFace : bottom O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+(72/25)*W.c)
    (order : O.s≤t) (small : t≤51/100) (wide : 43/50≤W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loV+L.side≤lower W r L.c) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0<W.c := by linarith only [wide]
  let H := O.s*L.c+O.c*r
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 lc.le) (mul_nonneg hc.le ln.1)
  have incoming := singleton_lower O L r on ln ls lBox ol
  change L.c*(O.loV+O.side)+L.side*L.c*H≤O.c*L.loV at incoming
  by_cases low : r≤t
  · let E := r*W.c-L.c*t
    have cosine := cosine_order wn ln low
    have en : E≤0 := by
      have first := mul_nonneg hd.le (sub_nonneg.mpr low)
      have second := mul_nonneg wn.1 (sub_nonneg.mpr cosine)
      dsimp [E]; nlinarith only [first,second]
    have wall := CornerWallNegativeShared.wall_support W t L.c r wn ln ws low wBox top
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
    have combined : W.c*L.c*(O.loV+O.side)+L.side*Q≤O.c*L.c*(t+(72/25)*W.c) := by
      dsimp [Q,E]
      nlinarith only [first,second,third]
    have scalar := CornerWallNegativeMixedBounds.low_margin on wn ln order low small wide
    have identity :
        (O.c*W.c)*(1+(L.c/O.c)*bottom O.c O.s+L.c*H/O.c+
          L.c/W.c-E-(L.c/W.c)*(t+(72/25)*W.c))=
        W.c*L.c*bottom O.c O.s+Q-O.c*L.c*(t+(72/25)*W.c) := by
      dsimp [Q]
      field_simp [ne_of_gt hc,ne_of_gt hd]
      <;> ring
    have scalarScaled := mul_pos (mul_pos hc hd) scalar
    have width := mul_pos (sub_pos.mpr side) qp
    have face := mul_pos (mul_pos hd lc) (sub_pos.mpr bottomFace)
    dsimp [H,E] at identity
    nlinarith only [combined,identity,scalarScaled,width,face]
  · have high : t≤r := (lt_of_not_ge low).le
    let E := r*W.c-L.c*t
    let K := r*t+L.c*W.c
    have kp : 0≤K := add_nonneg (mul_nonneg ln.1 wn.1) (mul_nonneg lc.le hd.le)
    have wall := marker_support W t L.c r wn ln ws high wMarker top
    rw [←same] at wall
    have first := mul_nonneg hc.le (sub_nonneg.mpr wall)
    have second := mul_nonneg hc.le (sub_nonneg.mpr lw)
    let Q := L.c*H+O.c*(1+K)
    have qp : 0<Q := by
      have p0 := mul_nonneg lc.le hp
      have p1 := mul_pos hc (show 0<1+K by linarith only [kp])
      dsimp [Q]; linarith only [p0,p1]
    have combined : L.c*(O.loV+O.side)+L.side*Q≤
        O.c*(E*((457/500)*W.c-2*t)+K*(t+(72/25)*W.c)) := by
      dsimp [Q,E,K]
      nlinarith only [incoming,first,second]
    have scalar := CornerWallNegativeMixedBounds.high_margin on wn ln order small wide
    have identity :
        O.c*(1+(L.c/O.c)*bottom O.c O.s+L.c*H/O.c+K-
          E*((457/500)*W.c-2*t)-K*(t+(72/25)*W.c))=
        L.c*bottom O.c O.s+Q-
          O.c*(E*((457/500)*W.c-2*t)+K*(t+(72/25)*W.c)) := by
      dsimp [Q]
      field_simp [ne_of_gt hc]
      <;> ring
    have scalarScaled := mul_nonneg hc.le scalar
    have width := mul_pos (sub_pos.mpr side) qp
    have face := mul_pos lc (sub_pos.mpr bottomFace)
    dsimp [H,E,K] at identity
    nlinarith only [combined,identity,scalarScaled,width,face]

end N12Compact.CornerWallNegativeMixed
