import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Completion.C1092.MPPMPositiveRetainingSteepScalars
import Compact.Completion.C1092.MPPMPositiveRetainingFirstNormals

/-! POSITIVE-RETAINING-ANGLE-AND-ORIGINS Theorem1, for the actual two
physical squares and their simultaneous faces. The steep endpoint is
included. No upper side cap or angle partition is assumed. Source only,
uncompiled; the original-family producers are separate obligations. -/
namespace N12Compact.C1092MPPMPositiveRetainingSteep
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports Scalars
set_option Elab.async false

structure Input (C E : OpenSquare) extends
    C1092MPPMPositiveRetainingFirstNormals.Input C E : Prop where
  lowerK : C.side+(2/5)*C.s-C.c≤C.loV+C.side
  capAE : E.loV+E.side≤0
  steep : 3/5≤E.s
  lowKE : C.side-E.c/2≤-E.loU
  markerC : C.Inside (-7/20) (-7/20)
  markerE : E.Inside (7/20) (-7/20)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

private theorem first_normals (C E : OpenSquare) (h : Input C E) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
  have cb := canonical_bounds h.central
  have eb := canonical_bounds h.recipient
  have rightward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx := by
    have first := (strict_bounds C _ _ nx ny unit h.markerC).2
    have last := (strict_bounds E _ _ nx ny unit h.markerE).1
    linarith only [first,last,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower C nx ny) :
      upper C (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [Completion.OtherCases.WallProfile.upper_neg,Completion.OtherCases.WallProfile.lower_neg]
    linarith only [sep]
  have choices := CongruentSAT.faceSeparation_of_disjoint C E h.same h.apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at choices
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius E nx ny=radius)
      (sep : radius≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [eq])
  rcases choices with cu|cv|eu|ev
  · rcases split _ _ _ (parallel_radius C E) cu with direct|back
    · left; simpa only [(ownU C).2] using direct
    · have no := rightward (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse _ _ back)
      exact False.elim (by linarith only [no,cb.1])
  · rcases split _ _ _ (transverse_radius C E) cv with direct|back
    · have no := rightward (-C.s) C.c (by nlinarith only [C.unit_normal]) direct
      exact False.elim (by linarith only [no,h.central.1])
    · have sep : upper C C.s (-C.c)≤lower E C.s (-C.c) := by
        simpa only [neg_neg] using reverse _ _ back
      exact False.elim (C1092MPPMPositiveRetainingFirstNormals.transverse_C C E h.toInput sep)
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases split _ _ _ radius eu with direct|back
    · right; simpa only [(ownU E).1] using direct
    · have no := rightward (-E.c) (-E.s) (by nlinarith only [E.unit_normal])
        (reverse _ _ back)
      exact False.elim (by linarith only [no,eb.1])
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases split _ _ _ radius ev with direct|back
    · have no := rightward (-E.s) E.c (by nlinarith only [E.unit_normal]) direct
      exact False.elim (by linarith only [no,h.recipient.1])
    · have sep : upper C E.s (-E.c)≤lower E E.s (-E.c) := by
        simpa only [neg_neg] using reverse _ _ back
      exact False.elim (C1092MPPMPositiveRetainingFirstNormals.transverse_E C E h.toInput sep)

private theorem no_current (C E : OpenSquare) (h : Input C E) :
    ¬C.loU+C.side≤lower E C.c C.s := by
  intro separation
  let k := kappa C.c C.s E.c E.s
  let z := sigma C.c C.s E.c E.s
  have rel := relative_bounds h.central h.recipient
  have kp : 0<k := by dsimp [k]; linarith only [rel.1]
  have du : C.c*E.c+C.s*E.s=k := rfl
  have dv : -C.c*E.s+C.s*E.c= -z := by dsimp [z,sigma]; ring
  have first : 0≤C.loU+C.side-(C.side-C.c-C.s) := sub_nonneg.mpr h.lowerA
  have recipient := mul_nonneg kp.le
    (show 0≤-E.loU-(C.side-E.c/2) by linarith only [h.lowKE])
  by_cases order : 0≤z
  · have formula := lower_pn E C.c C.s k (-z) du dv kp.le
      (by linarith only [order])
    rw [←h.same] at formula
    have nearAE : 0≤E.loV+C.side+(13/50)*E.c := by
      have near := h.nearAE
      rw [←h.same] at near
      linarith only [near]
    have last := mul_nonneg order nearAE
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<1+k by linarith only [kp])
    have margin := u_positive h.central h.recipient h.steep order
    have identity : (C.loU+C.side)+k*(-E.loU)+z*(E.loV+C.side)=
        uPlus C.c C.s E.c E.s+(C.side-1)*(1+k)+
          (C.loU+C.side-(C.side-C.c-C.s))+
          k*(-E.loU-(C.side-E.c/2))+z*(E.loV+C.side+(13/50)*E.c) := by
      dsimp [uPlus,k,z]
      ring
    nlinarith only [formula,separation,margin,strict,first,recipient,last,identity]
  · have order : z≤0 := (lt_of_not_ge order).le
    have formula := lower_nn E C.c C.s k (-z) du dv kp.le
      (by linarith only [order])
    have capAE : E.loV+C.side≤0 := by simpa only [h.same] using h.capAE
    have last := mul_nonneg_of_nonpos_of_nonpos order capAE
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<1+k-z by linarith only [kp,order])
    have margin := u_negative h.central h.recipient h.steep order
    have identity : (C.loU+C.side)+k*(-E.loU)+z*(E.loV+C.side)-C.side*z=
        uMinus C.c C.s E.c E.s+(C.side-1)*(1+k-z)+
          (C.loU+C.side-(C.side-C.c-C.s))+
          k*(-E.loU-(C.side-E.c/2))+z*(E.loV+C.side) := by
      dsimp [uMinus,k,z]
      ring
    nlinarith only [formula,separation,margin,strict,first,recipient,last,identity]

private theorem no_recipient (C E : OpenSquare) (h : Input C E) :
    ¬upper C E.c E.s≤E.loU := by
  intro separation
  let k := kappa C.c C.s E.c E.s
  let z := sigma C.c C.s E.c E.s
  have rel := relative_bounds h.central h.recipient
  have kp : 0<k := by dsimp [k]; linarith only [rel.1]
  have du : E.c*C.c+E.s*C.s=k := by dsimp [k,kappa]; ring
  have dv : -E.c*C.s+E.s*C.c=z := by dsimp [z,sigma]; ring
  have first : 0≤-E.loU-(C.side-E.c/2) := sub_nonneg.mpr h.lowKE
  have central := mul_nonneg kp.le
    (show 0≤C.loU+C.side-(C.side-C.c-C.s) by linarith only [h.lowerA])
  by_cases order : 0≤z
  · have formula := (formulas C E.c E.s).2
    rw [du,dv,max_eq_left kp.le,max_eq_left order] at formula
    have last := mul_nonneg order
      (show 0≤C.loV+C.side-(C.side+(2/5)*C.s-C.c) by linarith only [h.lowerK])
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<1+k+z by linarith only [kp,order])
    have margin := e_positive h.central h.recipient h.steep order
    have identity : -E.loU+k*(C.loU+C.side)+z*(C.loV+C.side)=
        ePlus C.c C.s E.c E.s+(C.side-1)*(1+k+z)+
          (-E.loU-(C.side-E.c/2))+
          k*(C.loU+C.side-(C.side-C.c-C.s))+
          z*(C.loV+C.side-(C.side+(2/5)*C.s-C.c)) := by
      dsimp [ePlus,k,z]
      ring
    nlinarith only [formula,separation,margin,strict,first,central,last,identity]
  · have order : z≤0 := (lt_of_not_ge order).le
    have formula := (formulas C E.c E.s).2
    rw [du,dv,max_eq_left kp.le,max_eq_right order] at formula
    have last := mul_nonneg_of_nonpos_of_nonpos order
      (show C.loV+C.side-C.s≤0 by linarith only [h.upperK])
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<1+k-z by linarith only [kp,order])
    have margin := e_negative h.central h.recipient h.steep order
    have identity : -E.loU+k*(C.loU+C.side)+z*(C.loV+C.side)-C.side*z=
        eMinus C.c C.s E.c E.s+(C.side-1)*(1+k-z)+
          (-E.loU-(C.side-E.c/2))+
          k*(C.loU+C.side-(C.side-C.c-C.s))+
          z*(C.loV+C.side-C.s) := by
      dsimp [eMinus,k,z]
      ring
    nlinarith only [formula,separation,margin,strict,first,central,last,identity]

/-- A steep positive retaining recipient cannot coexist with its genuine
positive predecessor. Every possible actual signed SAT source fails. -/
theorem impossible (C E : OpenSquare) (h : Input C E) : False := by
  rcases first_normals C E h with current|recipient
  · exact no_current C E h current
  · exact no_recipient C E h recipient

#print axioms impossible
end N12Compact.C1092MPPMPositiveRetainingSteep
