import Compact.Completion.C1092.MPPMInwardOuterFarEndpoints
import Compact.Completion.C1092.MPPMInwardOmittedFarBar

/-! Complete local endings of OUTER-OWNED-INWARD-FAR-ENDING and
CENTERED-OUTER-OWNED-FAR-ENDING. The common successor profile is the
existing actual point-and-bar theorem. The additional bottom origin
and the entire longer segment retain their genuine physical owners. -/
namespace N12Compact.C1092MPPMInwardOuterFar
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WallProfileScalars C1092WholeSupports
open C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

structure Input (C E R : OpenSquare) : Prop where
  side : 1<C.side
  normal : Normal C.c (-C.s)
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  crosspoint : C.Inside (-1/2) 0
  floor : -C.c-(13/50)*C.s≤C.loU
  successor : NegativeSuccessor E
  same : C.side=E.side
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  bottom : ¬E.Inside 0 (-1)
  bar : ∀ y : ℝ,-14/25≤y → y≤0 → R.Inside 1 y
  apartBar : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)

/-- The lower transverse face is strengthened by the genuine bottom
origin. Its simultaneous far upper face comes from the actual bar. -/
theorem far_profile (E R : OpenSquare) (side : 1<E.side) (e : NegativeSuccessor E)
    (bottom : ¬E.Inside 0 (-1))
    (bar : ∀ y : ℝ,-14/25≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) :
    -E.c≤E.loV ∧ E.loV+E.side≤-E.s-(14/25)*E.c ∧ 7/18<half E.c (-E.s) := by
  have far := C1092MPPMInwardOmittedFar.far_cap E R side e bar apart
  have ep : 0<E.c := by linarith only [(normal_bounds e.normal).1]
  have weaker : E.loV+E.side≤-E.s-(36/85)*E.c := by linarith only [far.1,ep]
  have floor := successor_bottom E side e weaker bottom
  have angle := width_half (11/25) e.normal (by norm_num)
    (show 1< -E.s+(11/25)*E.c by linarith only [floor.1,far.1,side])
  exact ⟨floor.1,far.1,by norm_num at angle; exact angle⟩

private theorem ending (C E R : OpenSquare) (h : Input C E R) (eta : ℝ)
    (cap : half C.c (-C.s)≤279/1000) (height : C.loV+C.side≤eta)
    (recipient : 0<recipientGap eta C.c (-C.s) E.c (-E.s)) : False := by
  have sideE : 1<E.side := by rw [←h.same]; exact h.side
  have profile := far_profile E R sideE h.successor h.bottom h.bar h.apartBar
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let a := C.side
  let k := c*d+s*t
  let z := c*t-s*d
  have cn : Normal c s := h.normal
  have en : Normal d t := h.successor.normal
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have dp : 0<d := by linarith only [(normal_bounds en).1]
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_nonneg cn.1 en.1
    dsimp only [k]
    nlinarith only [first,last]
  have zp : 0<z := C1092MPPMInwardFinal.relative_order cn en
    (show half c s<half d t by linarith only [cap,profile.2.2])
  have margin := central_positive cn en profile.2.2
  change 0<alpha c s+k*(1-d-t)+z*(1-t+(14/25)*d) at margin
  change 0<1-d-t+k*alpha c s+(1-eta)*z at recipient
  have alphaEq : alpha c s=1-c+(13/50)*s := rfl
  have lowerA : a-c+(13/50)*s≤C.loU+C.side := by
    dsimp only [a,c,s]
    linarith only [h.floor]
  have upperL : E.loU≤d+t-a := by
    dsimp only [a,d,t]
    rw [h.same]
    linarith only [h.successor.upperU]
  have upperK : E.loV≤t-(14/25)*d-a := by
    dsimp only [a,d,t]
    rw [h.same]
    linarith only [profile.2.1]
  have cu : C.c*E.c+C.s*E.s=k := by dsimp only [c,s,d,t,k]; ring
  have cv : -C.c*E.s+C.s*E.c=z := by dsimp only [c,s,d,t,z]; ring
  have eu : E.c*C.c+E.s*C.s=k := by dsimp only [c,s,d,t,k]; ring
  have ev : -E.c*C.s+E.s*C.c= -z := by dsimp only [c,s,d,t,z]; ring
  have excess := mul_pos (show 0<a-1 by exact sub_pos.mpr h.side)
    (show 0<1+k+z by linarith only [kp,zp])
  rcases longitudinal_axes C E h.same cn en h.marker h.successor.marker
      h.inner h.successor.halfpoint h.apart with current|next
  · have formula := lower_nn E C.c C.s k z cu cv kp.le zp.le
    have first := mul_le_mul_of_nonneg_left upperL kp.le
    have last := mul_le_mul_of_nonneg_left upperK zp.le
    rw [formula] at current
    nlinarith only [current,lowerA,first,last,margin,alphaEq,excess]
  · have formula : upper C E.c E.s=k*(C.loU+C.side)-z*C.loV := by
      rw [(formulas C E.c E.s).2,eu,ev,max_eq_left kp.le,max_eq_right (neg_nonpos.mpr zp.le)]
      ring
    have first := mul_le_mul_of_nonneg_left lowerA kp.le
    have last := mul_le_mul_of_nonneg_left height zp.le
    rw [formula] at next
    rw [alphaEq] at recipient
    nlinarith only [next,upperL,first,last,recipient,alphaEq,excess]

theorem missing_center_impossible (C E R : OpenSquare) (h : Input C E R)
    (cap : half C.c (-C.s)≤279/1000) (height : C.loV+C.side≤0) : False := by
  have sideE : 1<E.side := by rw [←h.same]; exact h.side
  have profile := far_profile E R sideE h.successor h.bottom h.bar h.apartBar
  exact ending C E R h 0 cap height
    (missing_recipient_positive h.normal h.successor.normal cap profile.2.2)

theorem centered_impossible (C E R : OpenSquare) (h : Input C E R)
    (cap : half C.c (-C.s)≤21/100) (height : C.loV+C.side≤17/125) : False := by
  have sideE : 1<E.side := by rw [←h.same]; exact h.side
  have profile := far_profile E R sideE h.successor h.bottom h.bar h.apartBar
  exact ending C E R h (17/125) (by linarith only [cap]) height
    (centered_recipient_positive h.normal h.successor.normal cap profile.2.2)

end
#print axioms far_profile
#print axioms missing_center_impossible
#print axioms centered_impossible
end N12Compact.C1092MPPMInwardOuterFar
