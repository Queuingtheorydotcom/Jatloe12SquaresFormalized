import Compact.Completion.C1092.MPPMOnePositiveClearance

/-! Complete raw Lemma 2 of ONE-POSITIVE-CONTINUOUS-ENDING. The
eight oriented actual normals reduce to three; clearance, the exact
positive longitudinal scalar and the simultaneous transverse faces
exclude them all. No preceding sign or invented origin owner is used. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports Completion.OtherCases
set_option Elab.async false
noncomputable section

private theorem positive_missing_axes (C E B : OpenSquare) (h : PositiveMissingInput C E B) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU ∨
      upper C E.s (-E.c)≤-(E.loV+E.side) := by
  have cb := normal_bounds h.source.normal
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [cb.1]
  have ep : 0<E.c := by linarith only [eb.1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx ∧ 0<(13/50)*nx-ny/2 := by
    have source := (strict_bounds C _ _ nx ny unit h.source.marker).2
    have recipient := (strict_bounds E _ _ nx ny unit h.marker).1
    have forward := (strict_bounds C _ _ nx ny unit h.source.forward).2
    have cross := (strict_bounds E _ _ nx ny unit h.crosspoint).1
    constructor <;> linarith only [source,recipient,forward,cross,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C E h.same h.apart
      with a|b|c|d|e|f|g|j
  · exact Or.inl (by simpa only [(ownU C).2] using a)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) b).1
    exact False.elim (by linarith only [no,cp])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) c).2
    exact False.elim (by linarith only [no,h.source.normal.2.1,cp])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) d).1
    exact False.elim (by linarith only [no,h.source.normal.1])
  · exact Or.inr (Or.inl (by simpa only [(ownU E).1] using e))
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) f).1
    exact False.elim (by linarith only [no,ep])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) g).1
    exact False.elim (by linarith only [no,h.recipient.1])
  · have formula : lower E E.s (-E.c)=-(E.loV+E.side) := by
      have neg := C1092TwoFifths.Support.lower_neg E (-E.s) E.c
      simpa only [neg_neg,(ownV E).2] using neg
    exact Or.inr (Or.inr (by simpa only [formula] using j))

/-- A narrow retaining negative owner cannot precede a positive missing
owner with its genuine strict crosspoint and missing-profile faces. -/
theorem positive_missing_impossible (C E B : OpenSquare) (h : PositiveMissingInput C E B) : False := by
  have f := C1092MPPMAllNonpositive.faces C h.source
  have cb := normal_bounds h.source.normal
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [h.close]
  have sp : 0< -C.s := by linarith only [f.negative]
  have dp : 0<E.c := by linarith only [eb.1]
  have small : -C.s<1/4 := by linarith only [h.small,cb.2.1]
  let k := C.c*E.c+C.s*E.s
  let ell := C.c*E.s-C.s*E.c
  have kp : 1/2<k := by
    have first := mul_nonneg sp.le (sub_nonneg.mpr h.recipient.2.1)
    have last := mul_nonneg (show 0≤E.c-7/10 by linarith only [eb.1])
      (show 0≤C.c+C.s by linarith only [h.close,small])
    dsimp [k]
    nlinarith only [first,last,h.close,small]
  have ep : 0<ell := by
    have first := mul_pos sp dp
    have last := mul_nonneg cp.le h.recipient.1
    dsimp [ell]
    nlinarith only [first,last]
  have strict := mul_pos (sub_pos.mpr h.source.side)
    (show 0<1+k+ell by linarith only [kp,ep])
  rcases positive_missing_axes C E B h with current|upward|downward
  · have formula := lower_pn E C.c C.s k (-ell)
      (by dsimp [k]; ring) (by dsimp [ell]; ring) (by linarith only [kp])
      (by linarith only [ep])
    have upper := mul_le_mul_of_nonneg_left h.upperU (show 0≤k by linarith only [kp])
    have lower := mul_le_mul_of_nonneg_left h.lowerV ep.le
    rw [←h.same] at upper formula
    have scalar := positive_longitudinal C.c (-C.s) E.c E.s h.source.normal h.close.le
      h.small.le h.recipient h.large
    have identity : 1-C.c+k*(1-E.c+(14/25)*E.s)+ell*(1-E.c-E.s)=
        1-positiveP E.c E.s*C.c-positiveQ E.c E.s*(-C.s) := by
      dsimp [k,ell,positiveP,positiveQ]
      linear_combination -(C.c-C.s)*E.unit_normal
    nlinarith only [current,formula,upper,lower,scalar,identity,strict,f.lowerU]
  · have support := positive_missing_upward C E B h
    have cross := h.crosspoint.1
    linarith only [upward,support,cross]
  · have formula := C1092TwoFifths.Support.upper_pos_neg C E.s (-E.c) ell (-k)
      (by dsimp [ell]; ring) (by dsimp [k]; ring) ep.le (by linarith only [kp])
    have first := mul_nonneg ep.le (show 0≤C.loU+C.c by linarith only [f.lowerU])
    have last := mul_nonneg (show 0≤k by linarith only [kp])
      (show 0≤43/500-C.loV-C.side by linarith only [h.height])
    have radial := mul_nonneg ep.le (show 0≤1-C.c by linarith only [cb.2.1])
    have height := mul_nonneg (show 0≤k-1/2 by linarith only [kp])
      (show (0:ℝ)≤1-43/500 by norm_num)
    have gap : 0<1-E.c-E.s+ell*(1-C.c)+k*(1-43/500) := by
      nlinarith only [radial,height,eb.2.2.2.2.2]
    rw [←h.same] at downward
    nlinarith only [downward,formula,first,last,h.lowerV,strict,gap]

end
#print axioms positive_missing_impossible
end N12Compact.C1092MPPMOnePositive
