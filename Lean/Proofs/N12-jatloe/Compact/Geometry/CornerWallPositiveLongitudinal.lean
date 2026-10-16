import Compact.Geometry.CornerWallSharedAxis

noncomputable section

/-! Original-support reduction for positive L's remaining longitudinal
separator. Unlike the earlier local exclusion, this does not require W
to miss (1,2). The two continuous scalar margins remain explicit until
their independent proofs are supplied. -/
namespace N12Compact.CornerWallPositiveLongitudinal

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner CornerWallCycleBounds

def X (d t : ℝ) : ℝ := 2*t^2+(43/500)*d*t+(72/25)*d^2-d
def Y (d t : ℝ) : ℝ := (457/500)*d^2+t^2+(22/25)*d*t-t

/-- The actual W marker and foreign top seed bound its lower support
on positive L's U axis, without any assumed W upper-U face. -/
theorem marker_support (W : OpenSquare) (t l r : ℝ)
    (wn : Normal W.c t) (ln : Normal l r) (ws : W.s=-t)
    (marker : W.Inside (457/500) 2)
    (top : W.loV+W.side≤t+(72/25)*W.c) :
    lower W l r+(W.side-1)*(l*t+r*W.c)≤l*Y W.c t+r*X W.c t := by
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
  have owned := (negative_bands W t _ _ ws).mp marker
  have first := mul_nonneg kp (sub_nonneg.mpr owned.1.le)
  have second := mul_nonneg hp (sub_nonneg.mpr top)
  have identity :
      k*((457/500)*W.c-2*t)+h*(t+(72/25)*W.c-1)=l*Y W.c t+r*X W.c t := by
    dsimp [k,h,X,Y]; ring
  dsimp [h] at form first second identity
  clear_value k
  nlinarith only [form,first,second,identity]

/-- The real left wall of positive L bounds its upper U face from an
O-v separator. The support bound is valid in both relative angle orders. -/
theorem incoming (O L : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s)
    (box : InsideContainer L)
    (ol : O.loV+O.side≤lower L (-O.s) O.c) :
    L.s*(O.loV+O.side)+L.side*(O.c+L.s*(O.c*L.c+O.s*L.s))≤
      O.c*(L.loU+L.side) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have hc : 0≤O.c := by linarith only [ob.1]
  have lc : 0≤L.c := by linarith only [lb.1]
  let D := O.c*L.s-O.s*L.c
  let K := O.c*L.c+O.s*L.s
  have kp : 0≤K := add_nonneg (mul_nonneg hc lc) (mul_nonneg on.1 ln.1)
  have form := lower_in_bands L (-O.s) O.c
  rw [show (-O.s)*L.c+O.c*L.s=D by dsimp [D]; ring,
    show -(-O.s)*L.s+O.c*L.c=K by dsimp [K]; ring,
    abs_of_nonneg kp] at form
  have width := mul_nonneg L.side_pos.le (sub_nonneg.mpr (le_abs_self D))
  have corner : lower L (-O.s) O.c≤D*L.loU+K*L.loV := by
    clear_value D K
    nlinarith only [form,width]
  have wall0 := FourSquareBLBridge.left_wall L lc box
  rw [abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  have wall : 0≤L.c*L.loU-L.s*(L.loV+L.side) := by nlinarith only [wall0]
  have first := mul_nonneg kp wall
  have second := mul_nonneg ln.1 (sub_nonneg.mpr (le_trans ol corner))
  have identity :
      O.c*(L.loU+L.side)-L.s*(O.loV+O.side)-L.side*(O.c+L.s*K)=
        K*(L.c*L.loU-L.s*(L.loV+L.side))+
          L.s*(D*L.loU+K*L.loV-(O.loV+O.side)) := by
    dsimp [D,K]
    linear_combination -O.c*L.loU*ln.2.2
  dsimp [K] at identity first second
  nlinarith only [identity,first,second]

/-- O-v / L-U reduces to the first displayed scalar. The full side
strictness is retained even at a zero-tilt endpoint. -/
theorem bottom_axis_of_margin (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side) (same : L.side=W.side)
    (lBox : InsideContainer L) (wMarker : W.Inside (457/500) 2)
    (bottomFace : bottom O.c O.s<O.loV+O.side)
    (top : W.loV+W.side≤t+(72/25)*W.c)
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (lw : L.loU+L.side≤lower W L.c L.s)
    (margin : 0≤1+(L.s/O.c)*bottom O.c O.s+
      (L.s/O.c)*(O.c*L.c+O.s*L.s)-L.c*Y W.c t-L.s*X W.c t) : False := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have hc : 0<O.c := by linarith only [ob.1]
  have hd : 0≤W.c := by linarith only [wb.1]
  have lc : 0≤L.c := by linarith only [lb.1]
  let K := O.c*L.c+O.s*L.s
  let h := L.c*t+L.s*W.c
  let Q := O.c+L.s*K+O.c*h
  have kp : 0≤K := add_nonneg (mul_nonneg hc.le lc) (mul_nonneg on.1 ln.1)
  have hp : 0≤h := add_nonneg (mul_nonneg lc wn.1) (mul_nonneg ln.1 hd)
  have qp : 0<Q := by
    have first := mul_nonneg ln.1 kp
    have second := mul_nonneg hc.le hp
    dsimp [Q]; linarith only [hc,first,second]
  have low := incoming O L on ln lBox ol
  have high := marker_support W t L.c L.s wn ln ws wMarker top
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
  clear_value Q h K
  nlinarith only [combined,identity,scaled,face,width]

/-- L-v / L-U reduces to the second displayed scalar. Here O's actual
bottom container and missing marker enter through its full lower support. -/
theorem singleton_axis_of_margin (O L W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (wn : Normal W.c t)
    (ws : W.s=-t) (side : 1<L.side)
    (sameOL : O.side=L.side) (sameLW : L.side=W.side)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oCap : O.loU+O.side≤2*O.c+O.s)
    (wMarker : W.Inside (457/500) 2)
    (top : W.loV+W.side≤t+(72/25)*W.c)
    (ol : upper O (-L.s) L.c≤L.loV)
    (lw : L.loU+L.side≤lower W L.c L.s)
    (margin : 0≤O.c*L.c+O.c*L.s+O.c*L.s*(O.c*L.c+O.s*L.s)+L.s^2-
      L.s^2*(2*O.c+O.s)-O.c*L.c*(L.c*Y W.c t+L.s*X W.c t)) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have wb := normal_bounds wn
  have hc : 0<O.c := by linarith only [ob.1]
  have lc : 0<L.c := by linarith only [lb.1]
  have hd : 0≤W.c := by linarith only [wb.1]
  let K := O.c*L.c+O.s*L.s
  let h := L.c*t+L.s*W.c
  have kp : 0≤K := add_nonneg (mul_nonneg hc.le lc.le) (mul_nonneg on.1 ln.1)
  have hp : 0≤h := add_nonneg (mul_nonneg lc.le wn.1) (mul_nonneg ln.1 hd)
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
  have high := marker_support W t L.c L.s wn ln ws wMarker top
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

end N12Compact.CornerWallPositiveLongitudinal
