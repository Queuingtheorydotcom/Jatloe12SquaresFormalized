import Compact.Completion.C1092.MPPMPositiveRetainingFirstNormalsScalars
import Compact.Completion.C1092.WholeSupports

/-! POSITIVE-RETAINING-FIRST-NORMALS Theorem 1. All faces belong to the
same actual two squares. Both relative angle orders and weak support
contact are included. This is a local direction theorem, not an original
family entrance or a cyclic contradiction. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMPositiveRetainingFirstNormals
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports
set_option Elab.async false

structure Input (C E : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  central : Normal C.c C.s
  recipient : Normal E.c E.s
  lowerA : C.side-C.c-C.s≤C.loU+C.side
  upperA : C.loU+C.side≤0
  upperK : C.loV+C.side≤C.s
  nearAE : -(13/50)*E.c<E.loV+E.side
  positiveKE : 0< -E.loU
  upperKE : -E.loU≤E.s

private theorem upper_opposite (Q : OpenSquare) : upper Q Q.s (-Q.c)= -Q.loV := by
  have du : Q.s*Q.c+(-Q.c)*Q.s=0 := by ring
  have dv : -Q.s*Q.s+(-Q.c)*Q.c= -1 := by nlinarith only [Q.unit_normal]
  rw [(formulas Q Q.s (-Q.c)).2,du,dv]
  norm_num

private theorem lower_opposite (Q : OpenSquare) :
    lower Q Q.s (-Q.c)= -(Q.loV+Q.side) := by
  have du : Q.s*Q.c+(-Q.c)*Q.s=0 := by ring
  have dv : -Q.s*Q.s+(-Q.c)*Q.c= -1 := by nlinarith only [Q.unit_normal]
  rw [(formulas Q Q.s (-Q.c)).1,du,dv]
  norm_num <;> ring

theorem transverse_C (C E : OpenSquare) (h : Input C E) :
    ¬upper C C.s (-C.c)≤lower E C.s (-C.c) := by
  intro separation
  let k := C.c*E.c+C.s*E.s
  let sigma := C.c*E.s-C.s*E.c
  have rel := relative h.central h.recipient
  have kp : 0<k := rel.1
  have base := transverse_base h.central h.recipient
  have strictAE := mul_pos kp
    (show 0<E.loV+E.side+(13/50)*E.c by linarith only [h.nearAE])
  have du : C.s*E.c+(-C.c)*E.s= -sigma := by dsimp [sigma]; ring
  have dv : -C.s*E.s+(-C.c)*E.c= -k := by dsimp [k]; ring
  rw [upper_opposite] at separation
  by_cases order : 0≤sigma
  · have formula := (formulas E C.s (-C.c)).1
    rw [du,dv,min_eq_left (by linarith only [order]),
      min_eq_left (by linarith only [kp])] at formula
    have face := mul_le_mul_of_nonneg_left h.upperKE order
    have sine := (normal_bounds h.recipient).2.2.2.1
    have angle := mul_nonpos_of_nonneg_of_nonpos order
      (show E.s-1≤0 by linarith only [sine])
    have strictSide := mul_pos (sub_pos.mpr h.side)
      (show 0<1+sigma by linarith only [order])
    rw [←h.same] at formula strictAE
    change C.s+(13/50)*k*E.c<1 at base
    nlinarith only [separation,formula,face,angle,strictSide,strictAE,h.upperK,base]
  · have order' : sigma≤0 := (lt_of_not_ge order).le
    have formula := lower_pn E C.s (-C.c) (-sigma) (-k) du dv
      (by linarith only [order']) (by linarith only [kp])
    have face := mul_nonpos_of_nonpos_of_nonneg order' h.positiveKE.le
    rw [←h.same] at formula strictAE
    change C.s+(13/50)*k*E.c<1 at base
    nlinarith only [separation,formula,face,strictAE,h.side,h.upperK,base]

theorem transverse_E (C E : OpenSquare) (h : Input C E) :
    ¬upper C E.s (-E.c)≤lower E E.s (-E.c) := by
  intro separation
  let k := C.c*E.c+C.s*E.s
  let sigma := C.c*E.s-C.s*E.c
  have rel := relative h.central h.recipient
  have kp : 0<k := rel.1
  have du : E.s*C.c+(-E.c)*C.s=sigma := by dsimp [sigma]; ring
  have dv : -E.s*C.s+(-E.c)*C.c= -k := by dsimp [k]; ring
  rw [lower_opposite] at separation
  have faceK := mul_le_mul_of_nonneg_left h.upperK kp.le
  by_cases order : 0≤sigma
  · have formula := (formulas C E.s (-E.c)).2
    rw [du,dv,max_eq_left order,max_eq_right (by linarith only [kp])] at formula
    have faceA := mul_le_mul_of_nonneg_left h.lowerA order
    have strictSide := mul_pos (sub_pos.mpr h.side)
      (show 0<k+sigma by linarith only [kp,order])
    have margin := successor_up h.central h.recipient
    change k*(C.s-1)+sigma*(C.c+C.s-1)+(13/50)*E.c<0 at margin
    rw [←h.same] at separation
    have nearAE : -(13/50)*E.c<E.loV+C.side := by simpa only [h.same] using h.nearAE
    nlinarith only [separation,formula,faceK,faceA,strictSide,nearAE,margin]
  · have order' : sigma≤0 := (lt_of_not_ge order).le
    have formula := (formulas C E.s (-E.c)).2
    rw [du,dv,max_eq_right order',max_eq_right (by linarith only [kp])] at formula
    have faceA := mul_nonneg (show 0≤-sigma by linarith only [order'])
      (show 0≤-(C.loU+C.side) by linarith only [h.upperA])
    have strictSide := mul_pos (sub_pos.mpr h.side)
      (show 0<k-sigma by linarith only [kp,order'])
    have margin := successor_down h.central h.recipient order'
    change k*(C.s-1)+sigma+(13/50)*E.c<0 at margin
    rw [←h.same] at separation
    have nearAE : -(13/50)*E.c<E.loV+C.side := by simpa only [h.same] using h.nearAE
    nlinarith only [separation,formula,faceK,faceA,strictSide,nearAE,margin]

#print axioms transverse_C
#print axioms transverse_E
end N12Compact.C1092MPPMPositiveRetainingFirstNormals
