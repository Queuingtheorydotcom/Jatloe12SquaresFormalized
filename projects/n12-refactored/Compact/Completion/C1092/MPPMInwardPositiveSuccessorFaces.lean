import Compact.Completion.C1092.MPPMInwardPositiveSuccessorScalars
import Compact.Completion.C1092.MPPMInwardNonnegativeFaces
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry

/-! Same-owner recipient faces for the positive missing-center inward
branch. The extra corner-marker exclusion is a literal actual Q1 marker
in the application; it permits reuse of the general ordinary face proof.
No opposite type or wall-origin ownership is assumed here. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

structure PairInput (C E : OpenSquare) : Prop where
  source : Input C
  same : C.side=E.side
  recipient : C1092MPPMInwardFinal.NonnegativeRecipient.Data E
  halfpoint : E.Inside (1/2) (-1)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

structure NonnegativeFaces (E : OpenSquare) : Prop where
  upperU : E.loU+E.side≤E.c-(2/5)*E.s
  lowerV : -E.c-E.s≤E.loV
  upperV : E.loV+E.side≤-E.c/2
  lowerU : -(543/500)*E.s≤E.loU
  large : 3/5<E.s
  cosine : E.c<4/5

theorem nonnegative_faces (C E : OpenSquare) (h : PairInput C E) (en : Normal E.c E.s) :
    NonnegativeFaces E := by
  have f := C1092MPPMInwardFinal.NonnegativeRecipient.faces E h.recipient en
  have eb := normal_bounds en
  have dp : 0<E.c := by linarith only [eb.1]
  have p := profile C h.source
  have lowU : E.loU< -E.s/2 := by
    apply lt_of_not_ge
    intro high
    have width : 1<E.c+(1/10)*E.s := by
      linarith only [high,f.1,h.recipient.side]
    have smallHalf := half_of_width en width
    have small := sine_le_twice_half en
    nlinarith only [smallHalf,small,f.2.1,f.2.2,h.recipient.side,eb.2.1]
  have upperV : E.loV+E.side≤-E.c/2 := by
    apply le_of_not_gt
    intro high
    apply h.apart 0 (-1/2)
    refine ⟨p.halfpoint,?_⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [lowU,high,h.recipient.successorMarker.2.1,h.recipient.near.2.2.1,
        dp,en.1,en.2.1]
  have lowerU : -(543/500)*E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply h.recipient.missingBottom
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,upperV,h.recipient.side,eb.2.1,h.recipient.near.2.1,
        h.recipient.successorMarker.2.2.2,dp,en.1,en.2.1]
  have width : 1<E.s+E.c/2 := by linarith only [upperV,f.2.2,h.recipient.side]
  have large : 3/5<E.s := by
    apply lt_of_not_ge
    intro low
    have bound := CommonCases.UnitCircleChord.increasing
      (c:=(4/5:ℝ)) (s:=3/5) (d:=E.c) (t:=E.s) (A:=1/2) (B:=1)
      (by norm_num) dp.le (by norm_num) E.unit_normal (by norm_num) en.1 low
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at bound
    linarith only [width,bound]
  have cosine : E.c<4/5 := by
    apply lt_of_not_ge
    intro high
    have first := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤E.c+4/5 by linarith only [dp])
    have last := mul_pos (sub_pos.mpr large)
      (show 0<E.s+3/5 by linarith only [en.1])
    nlinarith only [first,last,E.unit_normal]
  exact ⟨f.1,f.2.2,upperV,lowerU,large,cosine⟩

end
#print axioms nonnegative_faces
end N12Compact.C1092MPPMInwardPositive
