import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpointFaces

/-! Full local Theorem 1 of `C1092-MPPM-ORDINARY-NEGATIVE-HALFPOINT.md`.
Two actual disjoint squares, their literal strict anchors and two actual
source face caps force the successor's strict outer halfpoint. There are
no extra walls, angle restrictions, or upper side bound.

The original-family Corollary 2 additionally needs the missing-forward
predecessor cap producer and the positive-predecessor branches; those
are not asserted by this module. Source-only, not compiler acceptance. -/
namespace N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem point (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cp : 0<C.c) (cn : C.s≤0) (co : -C.s≤C.c)
    (ep : 0<E.c) (en : E.s≤0) (eo : -E.s≤E.c)
    (source : C.Inside (-7/20) (-7/20))
    (lowerCap : -(543/500)*C.c≤C.loU)
    (upperCap : C.loV+C.side≤(7/20)*(C.c+C.s))
    (target : E.Inside (7/20) (-7/20))
    (bar0 : E.Inside (13/50) (-1))
    (bar1 : E.Inside (2/5) (-1))
    (inner : E.Inside 0 (-13/50))
    (apart : ∀ x y, ¬(C.Inside x y ∧ E.Inside x y)) :
    E.Inside (1/2) (-1) := by
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let k := c*d+s*t
  let delta := c*t-s*d
  have cf : Frame c s := negative_frame C cp cn co
  have ef : Frame d t := negative_frame E ep en eo
  have kp : 0<k := (relative c s d t cf ef).1
  have coordinates := source_coordinates c s d t ef.unit
  have cosine : c=k*d+delta*t := coordinates.1
  have sine : s=k*t-delta*d := coordinates.2
  have capU : -(543/500)*c≤C.loU := lowerCap
  have capH : C.loV+C.side≤(7/20)*(c-s) := by
    dsimp [c,s]
    linarith only [upperCap]
  have lowH : -(7/20)*(c+s)<C.loV+C.side := by
    dsimp [c,s]
    linarith only [source.2.2.2]
  have lowK : E.loV<(13/50)*t-d := by
    dsimp [d,t]
    linarith only [bar0.2.2.1]
  have lowD : -(13/50)*d<E.loV+C.side := by
    dsimp [d]
    linarith only [inner.2.2.2,same]
  have eu : C.c*E.c+C.s*E.s=k := by dsimp [k,c,s,d,t]; ring
  have ev : -C.c*E.s+C.s*E.c=delta := by dsimp [delta,c,s,d,t]; ring
  have cu : E.c*C.c+E.s*C.s=k := by dsimp [k,c,s,d,t]; ring
  have cv : -E.c*C.s+E.s*C.c=-delta := by dsimp [delta,c,s,d,t]; ring
  by_contra missing
  have targetCap : E.loU+C.side≤d/2+t := by
    have h := missing_face E ef target bar1 missing
    dsimp [d,t]
    linarith only [h,same]
  have alternatives := axes C E same cf ef source target bar0 apart
  rcases alternatives with sourceAxis | targetAxis
  · by_cases order : 0≤delta
    · have support : lower E C.c C.s=k*E.loU+delta*E.loV :=
        C1092WholeSupports.lower_nn E C.c C.s k delta eu ev kp.le order
      rw [support] at sourceAxis
      have first := mul_le_mul_of_nonneg_left targetCap kp.le
      have second := mul_le_mul_of_nonneg_left lowK.le order
      have identity : (543/500)*c+k*(d/2+t)+delta*((13/50)*t-d)=
          (793/500)*c+s-(6/25)*delta*t := by
        linear_combination -(1/2)*cosine-sine
      have necessary : C.side*(1+k)≤(793/500)*c+s-(6/25)*delta*t := by
        nlinarith only [sourceAxis,capU,first,second,identity]
      have correction := mul_nonneg order ef.nonnegative
      have margin := c_positive c s d t cf ef order
      change (793/500)*c+s<1+k at margin
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+k by linarith only [kp])
      nlinarith only [necessary,correction,margin,strict]
    · have order' : delta≤0 := (lt_of_not_ge order).le
      have support : lower E C.c C.s=k*E.loU+delta*(E.loV+C.side) := by
        have h := C1092WholeSupports.lower_pn E C.c C.s k delta eu ev kp.le order'
        simpa only [←same] using h
      rw [support] at sourceAxis
      have first := mul_le_mul_of_nonneg_left targetCap kp.le
      have second := mul_le_mul_of_nonpos_left lowD.le order'
      have identity : (543/500)*c+k*(d/2+t)-delta*((13/50)*d)=
          (793/500)*c+s+delta*((37/50)*d-t/2) := by
        linear_combination -(1/2)*cosine-sine
      have necessary : C.side*(1+k)≤
          (793/500)*c+s+delta*((37/50)*d-t/2) := by
        nlinarith only [sourceAxis,capU,first,second,identity]
      have margin := c_negative c s d t cf ef order'
      change (793/500)*c+s+delta*((37/50)*d-t/2)<1+k at margin
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+k by linarith only [kp])
      nlinarith only [necessary,margin,strict]
  · by_cases order : 0≤delta
    · have support : upper C E.c E.s=k*(C.loU+C.side)-delta*C.loV := by
        rw [(C1092WholeSupports.formulas C E.c E.s).2,cu,cv,
          max_eq_left kp.le,max_eq_right (neg_nonpos.mpr order)]
        ring
      rw [support] at targetAxis
      have first := mul_le_mul_of_nonneg_left capU kp.le
      have second := mul_le_mul_of_nonneg_left capH order
      have necessary : C.side*(1+k+delta)≤
          (543/500)*k*c+(7/20)*delta*(c-s)+d/2+t := by
        nlinarith only [targetAxis,targetCap,first,second]
      have margin := e_positive c s d t cf ef order
      change (543/500)*k*c+(7/20)*delta*(c-s)+d/2+t<1+k+delta at margin
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+k+delta by linarith only [kp,order])
      nlinarith only [necessary,margin,strict]
    · have order' : delta≤0 := (lt_of_not_ge order).le
      have positive : 0≤-delta := neg_nonneg.mpr order'
      have support : upper C E.c E.s=
          k*(C.loU+C.side)+(-delta)*(C.loV+C.side) := by
        rw [(C1092WholeSupports.formulas C E.c E.s).2,cu,cv,
          max_eq_left kp.le,max_eq_left positive]
        ring
      rw [support] at targetAxis
      have first := mul_le_mul_of_nonneg_left capU kp.le
      have second := mul_le_mul_of_nonneg_left lowH.le positive
      have necessary : C.side*(1+k)≤
          (543/500)*k*c+(7/20)*(-delta)*(c+s)+d/2+t := by
        nlinarith only [targetAxis,targetCap,first,second]
      have margin := e_negative c s d t cf ef
      change d/2+t-k*(1-(543/500)*c)+(7/20)*(-delta)*(c+s)<1 at margin
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+k by linarith only [kp])
      nlinarith only [necessary,margin,strict]

end N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
