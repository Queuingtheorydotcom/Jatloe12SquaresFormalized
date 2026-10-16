import Compact.Completion.C1092.MPPMNegativeOwnedPositiveExclusionScalars
import Compact.Completion.C1092.MPPMNegativeForward
import Compact.Completion.C1092.TwoFifthsSupport

/-! Full raw NEGATIVE-OWNED-POSITIVE-OWNED-EXCLUSION Theorem 1.
The existing negative-forward input retains the same actual C,E,B and
the whole strict B segment. No backward-inner exclusion is added.
The angle premise is produced by NegativeOwnedPositiveCeiling in the
original-owner adapter. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeOwnedPositiveExclusion
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports Completion.OtherCases
set_option Elab.async false
noncomputable section

structure Input (C E B : OpenSquare) extends C1092MPPMNegativeForward.Input C E B : Prop where
  positive : 0<E.s
  half : E.s/(1+E.c)≤7/32
  corner : ¬E.Inside 1 (-1)
  far : ¬E.Inside 1 (-14/25)
  apartTargetBar : ∀ x y,¬(E.Inside x y ∧ B.Inside x y)

/-- The actual bottom origin and southeast corner force the lower
faces. The actual far right point then forces the upper first face. -/
theorem target_faces (C E B : OpenSquare) (h : Input C E B) :
    -E.s≤E.loU ∧ -E.c-E.s≤E.loV ∧ E.loU+E.side≤E.c-(14/25)*E.s := by
  have eb := normal_bounds h.targetNormal
  have dp : 0<E.c := by linarith only [eb.1]
  have angle := Scalars.recipient_bounds h.targetNormal h.half
  have eside : 1<E.side := by linarith only [h.side,h.same]
  have lowerU : -E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply h.apartTargetBar 0 (-1)
    refine ⟨?_,h.wholeBar 0 (by norm_num) (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.bar0.2.1,h.bar0.2.2.1,h.inner.2.2.2,dp,h.positive]
  have lowerV : -E.c-E.s≤E.loV := by
    apply le_of_not_gt
    intro low
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.bar1.1,h.bar1.2.2.2,lowerU,eside,eb.2.1,dp,h.positive]
  have upperU : E.loU+E.side≤E.c-(14/25)*E.s := by
    apply le_of_not_gt
    intro high
    apply h.far
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.bar1.1,h.bar1.2.2.1,h.target.2.2.2,dp,h.positive,angle.2]
  exact ⟨lowerU,lowerV,upperU⟩

/-- Every genuine separating axis fails, with the weak contact cases
kept. The actual predecessor marker cap is used in the last comparison. -/
theorem impossible (C E B : OpenSquare) (h : Input C E B) : False := by
  have f := C1092MPPMNegativeForward.source_profile C E B h.toInput
  have ef := target_faces C E B h
  have cb := normal_bounds h.sourceNormal
  have eb := normal_bounds h.targetNormal
  have cp : 0<C.c := by linarith only [f.close]
  have sp := f.negative
  have dp : 0<E.c := by linarith only [eb.1]
  let k := C.c*E.c+C.s*E.s
  let ell := C.c*E.s-C.s*E.c
  have kp : 0<k := by
    have first := mul_pos dp (show 0<C.c+C.s by linarith only [f.close,f.small])
    have last := mul_nonneg sp.le (sub_nonneg.mpr h.targetNormal.2.1)
    dsimp [k]
    nlinarith only [first,last]
  have ep : 0<ell := by
    have first := mul_pos sp dp
    have last := mul_nonneg cp.le h.targetNormal.1
    dsimp [ell]
    nlinarith only [first,last]
  have strict := mul_pos (sub_pos.mpr h.side)
    (show 0<1+k+ell by linarith only [kp,ep])
  rcases C1092MPPMNegativeForward.axes C E B h.toInput with own | upward | downward
  · have formula := lower_pn E C.c C.s k (-ell)
      (by dsimp [k]) (by dsimp [ell]; ring) kp.le (neg_nonpos.mpr ep.le)
    have upper := mul_le_mul_of_nonneg_left ef.2.2 kp.le
    have lower := mul_le_mul_of_nonneg_left ef.2.1 ep.le
    rw [←h.same] at upper formula
    have scalar := Scalars.longitudinal h.sourceNormal h.targetNormal h.positive h.half
    have identity : 1-C.c+k*(1-E.c+(14/25)*E.s)+ell*(1-E.c-E.s)=
        1-Scalars.Pu E.c E.s*C.c-Scalars.Qu E.c E.s*(-C.s) := by
      dsimp [k,ell,Scalars.Pu,Scalars.Qu]
      linear_combination -(C.c-C.s)*E.unit_normal
    nlinarith only [own,formula,upper,lower,scalar,identity,strict,f.lowerU]
  · have support := C1092MPPMNegativeForward.target_support C E B h.toInput f
    have anchor := h.inner.1
    linarith only [upward,support,anchor]
  · have formula := C1092TwoFifths.Support.upper_pos_neg C E.s (-E.c) ell (-k)
      (by dsimp [ell]; ring) (by dsimp [k]; ring) ep.le (neg_nonpos.mpr kp.le)
    have lower := mul_le_mul_of_nonneg_left f.lowerU ep.le
    have upper := mul_le_mul_of_nonneg_left f.upperV kp.le
    have angle := Scalars.recipient_bounds h.targetNormal h.half
    have scalar := Scalars.transverse h.sourceNormal f.close h.targetNormal angle.1
    have identity : 1+k+ell-E.c-E.s-ell*C.c-(7/20)*k*(C.c+C.s)=
        1-Scalars.Pf C.c (-C.s)*E.c-Scalars.Qf C.c (-C.s)*E.s := by
      dsimp [k,ell,Scalars.Pf,Scalars.Qf]
      linear_combination -E.s*C.unit_normal
    rw [←h.same] at downward
    nlinarith only [downward,formula,lower,upper,ef.2.1,strict,scalar,identity]

end
end N12Compact.C1092MPPMNegativeOwnedPositiveExclusion
