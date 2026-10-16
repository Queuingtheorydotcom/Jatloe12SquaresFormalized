import Compact.Completion.C1092.MPPMInwardFinalSignScalars
import S12.Diagonal
import Compact.Geometry.C977CornerSectorBounds

/-! Reusable ordinary recipient face comparisons. Every hypothesis
concerns this one actual E, independent of the preceding square's sign.
The corner-marker omission is an explicit foreign actual-owner datum. -/
namespace N12Compact.C1092MPPMInwardFinal.NonnegativeRecipient
open S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

structure Data (E : OpenSquare) : Prop where
  side : 1<E.side
  successorMarker : E.Inside (7/20) (-7/20)
  near : E.Inside (13/50) (-1)
  outer : E.Inside (2/5) (-1)
  missingInner : ¬E.Inside 0 (-13/50)
  missingRight : ¬E.Inside 1 (-2/5)
  missingBottom : ¬E.Inside 0 (-543/500)
  missingCorner : ¬E.Inside 1 (-1)
  missingCornerMarker : ¬E.Inside 1 (-543/500)

theorem faces (E : OpenSquare) (h : Data E) (en : Normal E.c E.s) :
    E.loU+E.side≤E.c-(2/5)*E.s ∧ E.loV+E.side≤-(13/50)*E.c ∧
      -E.c-E.s≤E.loV := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have side := h.side
  have capU : E.loU+E.side≤E.c-(2/5)*E.s := by
    apply le_of_not_gt
    intro high
    apply h.missingRight
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.successorMarker.1,h.outer.2.2.1,h.successorMarker.2.2.2,
        high,ep,en.1,en.2.1]
  have capV : E.loV+E.side≤-(13/50)*E.c := by
    apply le_of_not_gt
    intro high
    apply h.missingInner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [capU,side,eb.2.1,h.successorMarker.2.1,h.outer.2.2.1,
        high,ep,en.1,en.2.1]
  have floor : -E.c-E.s≤E.loV := by
    apply le_of_not_gt
    intro below
    have cornerU : E.loU+E.side≤E.c-E.s := by
      apply le_of_not_gt
      intro high
      apply h.missingCorner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.outer.1,h.successorMarker.2.2.2,below,high,ep,en.1,en.2.1]
    have bottomU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt
      intro low
      apply h.missingBottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,h.near.2.1,h.successorMarker.2.2.2,capV,side,eb.2.1,ep,en.1,en.2.1]
    have width : 1<E.c+(43/500)*E.s := by linarith only [bottomU,cornerU,side]
    have data := quarter_data E.c E.s ep.le en.1 en.2.2
    let z := half E.c E.s
    have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
    have identity : (1+z^2)*(E.c+(43/500)*E.s-1)=2*z*(43/500-z) := by
      nlinarith only [data.2.2.2.1,data.2.2.2.2]
    have positive := mul_pos den (sub_pos.mpr width)
    have smallHalf : z<43/500 := by
      apply lt_of_not_ge
      intro large
      have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*z by linarith only [data.1])
        (show 43/500-z≤0 by linarith only [large])
      nlinarith only [bad,identity,positive]
    have extra := mul_nonneg en.1 (sq_nonneg z)
    have small : E.s<43/250 := by nlinarith only [data.2.2.2.2,smallHalf,extra]
    have finalU : E.loU+E.side≤E.c-(543/500)*E.s := by
      apply le_of_not_gt
      intro high
      apply h.missingCornerMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.outer.1,h.successorMarker.2.2.2,capV,side,eb.2.1,
          high,small,ep,en.1,en.2.1]
    linarith only [finalU,bottomU,side,eb.2.1]
  exact ⟨capU,capV,floor⟩

#print axioms faces
end N12Compact.C1092MPPMInwardFinal.NonnegativeRecipient
