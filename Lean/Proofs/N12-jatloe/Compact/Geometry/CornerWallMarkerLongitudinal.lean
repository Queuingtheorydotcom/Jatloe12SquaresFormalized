import Compact.Geometry.CornerWallPositiveLongitudinal
import Compact.Geometry.NegativeWallMarkerCap

noncomputable section

/-! Positive-L longitudinal support using both genuine foreign markers.
The NW marker supplies W's upper U face, while the paired upper corner
marker supplies its upper V face. Both full side corrections are retained. -/
namespace N12Compact.CornerWallMarkerLongitudinal

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner CornerWallCycleBounds

def X (d t : ℝ) : ℝ := 3-(13/20)*t^2-(92/125)*d*t+t-d
def Y (d t : ℝ) : ℝ := 33/20-(92/125)*t^2+(13/20)*d*t-d-t
def H (d t l r : ℝ) : ℝ := l*d-r*t+l*t+r*d

theorem h_nonnegative {d t l r : ℝ} (wn : Normal d t) (ln : Normal l r) :
    0≤H d t l r := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hd : 0≤d := by linarith only [wb.1]
  have hl : 0≤l := by linarith only [lb.1]
  have first := mul_nonneg hd (sub_nonneg.mpr ln.2.1)
  have second := mul_nonneg ln.1 (sub_nonneg.mpr wn.2.1)
  have third := mul_nonneg hl wn.1
  have fourth := mul_nonneg ln.1 hd
  dsimp [H]
  nlinarith only [first,second,third,fourth]

/-- Both caps are consequences of actual marker exclusions, supplied by
NegativeWallMarkerCap.upper_u and upper_face. -/
theorem marker_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c) :
    lower W l r+(W.side-1)*H W.c t l r≤l*Y W.c t+r*X W.c t := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hd : 0≤W.c := by linarith only [wb.1]
  have lc : 0≤l := by linarith only [lb.1]
  let k := l*W.c-r*t
  let h := l*t+r*W.c
  have kp : 0≤k := by
    have first := mul_nonneg hd (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]; nlinarith only [first,second]
  have hp : 0≤h := add_nonneg (mul_nonneg lc wn.1) (mul_nonneg ln.1 hd)
  have form : lower W l r=k*W.loU+h*W.loV := by
    rw [lower_negative_pos W t l r ws kp hp]
  have first := mul_nonneg kp (sub_nonneg.mpr northwest)
  have second := mul_nonneg hp (sub_nonneg.mpr top)
  have identity :
      k*((33/20)*W.c-(47/20)*t-1)+h*((457/500)*t+3*W.c-1)=
        l*Y W.c t+r*X W.c t := by
    dsimp [k,h,X,Y]
    linear_combination ((33/20)*l+3*r)*wn.2.2
  have sum : H W.c t l r=k+h := by dsimp [H,k,h]; ring
  rw [sum]
  clear_value k h
  nlinarith only [form,first,second,identity]

/-- The O-v / L-U support contradiction with the genuine two caps. -/
theorem bottom_axis_of_margin (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L)
    (bottomFace : bottom O.c O.s<O.loV+O.side)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loU+L.side≤lower W L.c L.s)
    (margin : 0≤1+(L.s/O.c)*bottom O.c O.s+
      (L.s/O.c)*(O.c*L.c+O.s*L.s)-L.c*Y W.c t-L.s*X W.c t) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0≤L.c := by linarith only [lb.1]
  let K := O.c*L.c+O.s*L.s
  let h := H W.c t L.c L.s
  let Q := O.c+L.s*K+O.c*h
  have kp : 0≤K := add_nonneg (mul_nonneg hc.le lc) (mul_nonneg on.1 ln.1)
  have hp : 0≤h := h_nonnegative wn ln
  have qp : 0<Q := by
    have first := mul_nonneg ln.1 kp
    have second := mul_nonneg hc.le hp
    dsimp [Q]; linarith only [hc,first,second]
  have low := CornerWallPositiveLongitudinal.incoming O L on ln lBox ol
  have high := marker_support W t L.c L.s wn ln ws northwest top
  rw [←same] at high
  have selected := mul_nonneg hc.le (sub_nonneg.mpr lw)
  have upper := mul_nonneg hc.le (sub_nonneg.mpr high)
  have combined : L.s*(O.loV+O.side)+L.side*Q≤
      O.c*(L.c*Y W.c t+L.s*X W.c t+h) := by
    dsimp [Q,K,h]
    nlinarith only [low,selected,upper]
  have identity :
      O.c*(1+(L.s/O.c)*bottom O.c O.s+(L.s/O.c)*K-
        L.c*Y W.c t-L.s*X W.c t)=
      L.s*bottom O.c O.s+Q-O.c*(L.c*Y W.c t+L.s*X W.c t+h) := by
    dsimp [Q]
    field_simp [ne_of_gt hc]
    ring
  have scaled := mul_nonneg hc.le margin
  have face := mul_nonneg ln.1 (sub_nonneg.mpr bottomFace.le)
  have width := mul_pos (sub_pos.mpr side) qp
  dsimp [K] at identity
  clear_value K h Q
  nlinarith only [combined,identity,scaled,face,width]

/-- The L-v / L-U support contradiction. The weaker cap (2c+s)
already suffices, so the actual cap (2c+.914s) is retained by monotonicity. -/
theorem singleton_axis_of_margin (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+O.s)
    (northwest : W.loU+W.side≤(33/20)*W.c-(47/20)*t)
    (top : W.loV+W.side≤(457/500)*t+3*W.c)
    (ol : upper O (-L.s) L.c≤L.loV)
    (lw : L.loU+L.side≤lower W L.c L.s)
    (margin : 0≤O.c*L.c+O.c*L.s+O.c*L.s*(O.c*L.c+O.s*L.s)+L.s^2-
      L.s^2*(2*O.c+O.s)-O.c*L.c*(L.c*Y W.c t+L.s*X W.c t)) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  let K := O.c*L.c+O.s*L.s
  let h := H W.c t L.c L.s
  have kp : 0≤K := add_nonneg (mul_nonneg hc.le lc.le) (mul_nonneg on.1 ln.1)
  have hp : 0≤h := h_nonnegative wn ln
  have oside : 0<O.side := by rw [sameOL]; linarith only [side]
  have bottom := CornerWallSharedAxis.bottom_support O L.c L.s on lc.le ln.1 oside oBox oCap
  rw [sameOL] at bottom
  have wall0 := FourSquareBLBridge.left_wall L lc.le lBox
  rw [abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  have wall : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall0]
  have lowerWeighted := mul_nonneg ln.1 (sub_nonneg.mpr bottom)
  have firstSelected := mul_nonneg (mul_nonneg hc.le ln.1) (sub_nonneg.mpr ol)
  have wallWeighted := mul_nonneg hc.le wall
  have high := marker_support W t L.c L.s wn ln ws northwest top
  rw [←sameLW] at high
  have upperWeighted := mul_nonneg (mul_nonneg hc.le lc.le) (sub_nonneg.mpr high)
  have secondSelected := mul_nonneg (mul_nonneg hc.le lc.le) (sub_nonneg.mpr lw)
  let Q := O.c*L.c+O.c*L.s+L.s*(O.c*K+L.s)+O.c*L.c*h
  let R := L.s^2*(2*O.c+O.s)+O.c*L.c*(L.c*Y W.c t+L.s*X W.c t+h)
  have qp : 0<Q := by
    have first := mul_pos hc lc
    have second := mul_nonneg hc.le ln.1
    have third := mul_nonneg ln.1 (add_nonneg (mul_nonneg hc.le kp) ln.1)
    have fourth := mul_nonneg (mul_nonneg hc.le lc.le) hp
    dsimp [Q]; linarith only [first,second,third,fourth]
  have combined : L.side*Q≤R := by
    dsimp [Q,R,K,h]
    nlinarith only [lowerWeighted,firstSelected,wallWeighted,upperWeighted,secondSelected]
  have identity : Q-R=O.c*L.c+O.c*L.s+O.c*L.s*K+L.s^2-
      L.s^2*(2*O.c+O.s)-O.c*L.c*(L.c*Y W.c t+L.s*X W.c t) := by
    dsimp [Q,R]; ring
  have width := mul_pos (sub_pos.mpr side) qp
  dsimp [K] at identity
  nlinarith only [combined,identity,margin,width]

#print axioms marker_support
#print axioms bottom_axis_of_margin
#print axioms singleton_axis_of_margin
end N12Compact.CornerWallMarkerLongitudinal
