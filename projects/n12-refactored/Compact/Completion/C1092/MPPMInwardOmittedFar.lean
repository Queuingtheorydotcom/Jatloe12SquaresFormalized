import Compact.Completion.C1092.MPPMInwardOmittedFarScalars
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry

/-! Full local CENTERED-INWARD-OMITTED-G-FAR-ENDING. The genuine
omitted G point supplies the stronger source face; the same actual
successor and one actual foreign bar supply both support comparisons.
No bottom origin or supplementary wall is a premise. Source only. -/
namespace N12Compact.C1092MPPMInwardOmittedFar
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092MPPMInwardFinal C1092WallProfileScalars C1092WholeSupports
open Completion.OtherCases
set_option Elab.async false
noncomputable section

/-- The actual G omission has only its lower first-face exit once
the centered height and angle estimates have been supplied. -/
theorem omitted_lower (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (marker : C.Inside (-7/20) (-7/20))
    (small : half C.c (-C.s)≤21/100) (height : C.loV+C.side≤17/125)
    (missing : ¬C.Inside (-1) (-2/5)) : -C.c-(2/5)*C.s≤C.loU := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have bounds := Scalars.source_bounds cn small
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [low,marker.2.1,marker.2.2.2,height,side,cb.2.1,bounds.2,cp,cn.1,cn.2.1]

structure Input (C E R : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  normal : Normal C.c (-C.s)
  small : half C.c (-C.s)≤21/100
  lowerU : -C.c-(2/5)*C.s≤C.loU
  height : C.loV+C.side≤17/125
  marker : C.Inside (-7/20) (-7/20)
  crosspoint : C.Inside (-1/2) 0
  successor : NegativeSuccessor E
  bar : ∀ y : ℝ,-14/25≤y → y≤0 → R.Inside 1 y
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  apartBar : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)

private theorem axes (C E R : OpenSquare) (h : Input C E R) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.normal).1]
  have dp : 0<E.c := by linarith only [(normal_bounds h.successor.normal).1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx ∧ 0<nx-ny := by
    have first := (strict_bounds C _ _ nx ny unit h.marker).2
    have last := (strict_bounds E _ _ nx ny unit h.successor.marker).1
    have cross := (strict_bounds C _ _ nx ny unit h.crosspoint).2
    have halfpoint := (strict_bounds E _ _ nx ny unit h.successor.halfpoint).1
    constructor <;> linarith only [first,last,cross,halfpoint,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C E h.same h.apart
      with cu | cu' | cv | cv' | eu | eu' | ev | ev'
  · exact Or.inl (by simpa only [(ownU C).2] using cu)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) cu').1
    exact False.elim (by linarith only [no,cp])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) cv).2
    exact False.elim (by linarith only [no,h.normal.2.1])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) cv').1
    exact False.elim (by linarith only [no,h.normal.1])
  · exact Or.inr (by simpa only [(ownU E).1] using eu)
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) eu').1
    exact False.elim (by linarith only [no,dp])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) ev).2
    exact False.elim (by linarith only [no,h.successor.normal.2.1])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) ev').1
    exact False.elim (by linarith only [no,h.successor.normal.1])

theorem impossible (C E R : OpenSquare) (h : Input C E R) : False := by
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let k := c*d+s*t
  let delta := c*t-s*d
  have cn : Normal c s := h.normal
  have en : Normal d t := h.successor.normal
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  have bound := far_cap E R (by linarith only [h.side,h.same]) h.successor h.bar h.apartBar
  have large : 237/763≤half d t := bound.2.le
  have sourceBounds := Scalars.source_bounds cn h.small
  have targetBounds := Scalars.endpoint_order en large
  have tl : 14/25≤t := by
    have lower := targetBounds.2.2
    dsimp [Scalars.t0] at lower
    linarith only [lower]
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_nonneg cn.1 en.1
    dsimp [k]
    nlinarith only [first,last]
  have deltaPositive : 0<delta := by
    have first := mul_nonneg (show 0≤c-91/100 by linarith only [sourceBounds.1]) en.1
    have last := mul_nonneg cn.1 (show 0≤1-d by linarith only [eb.2.1])
    dsimp [delta]
    nlinarith only [first,last,sourceBounds.2,tl]
  have sourceFloor : -c+(2/5)*s≤C.loU := by
    dsimp [c,s]
    linarith only [h.lowerU]
  have highU : E.loU+C.side≤d+t := by
    dsimp [d,t]
    linarith only [h.successor.upperU,h.same]
  have highV : E.loV+C.side≤t-(14/25)*d := by
    dsimp [d,t]
    linarith only [bound.1,h.same]
  have strict := mul_pos (sub_pos.mpr h.side)
    (show 0<1+k+delta by linarith only [kp,deltaPositive])
  rcases axes C E R h with own | target
  · have formula := lower_nn E C.c C.s k delta
      (by dsimp [k,c,s,d,t]; ring) (by dsimp [delta,c,s,d,t]; ring) kp.le deltaPositive.le
    have first := mul_le_mul_of_nonneg_left highU kp.le
    have last := mul_le_mul_of_nonneg_left highV deltaPositive.le
    have margin := Scalars.source_positive cn en large
    change 0<1-c+(2/5)*s+k*(1-d-t)+delta*(1-t+(14/25)*d) at margin
    nlinarith only [own,formula,first,last,margin,sourceFloor,strict]
  · have formula := C1092TwoFifths.Support.upper_pos_neg C E.c E.s k (-delta)
      (by dsimp [k,c,s,d,t]; ring) (by dsimp [delta,c,s,d,t]; ring)
      kp.le (neg_nonpos.mpr deltaPositive.le)
    have first := mul_le_mul_of_nonneg_left sourceFloor kp.le
    have last := mul_le_mul_of_nonneg_left h.height deltaPositive.le
    have margin := Scalars.target_positive cn en h.small large
    change 1/100<1-d-t+k*(1-c+(2/5)*s)+delta*(108/125) at margin
    nlinarith only [target,formula,first,last,margin,highU,strict]

end
end N12Compact.C1092MPPMInwardOmittedFar
