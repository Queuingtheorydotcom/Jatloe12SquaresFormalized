import Compact.Completion.C1092.MPPMInwardNonnegativeFaces
import Compact.Completion.C1092.TwoFifthsSupport

/-! NEGATIVE-INWARD-SUCCESSOR-SIGN Theorem 1. The original lower
corner marker is retained as its own strict-owner exclusion. Both
canonical endpoints and every weak separating equality are covered. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

structure SignInput (C E : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  central : Normal C.c (-C.s)
  lowerA : C.side-C.c-(13/50)*C.s≤C.loU+C.side
  upperH : C.loV+C.side≤(7/20)*(C.c+C.s)
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  crosspoint : C.Inside (-1/2) 0
  successorMarker : E.Inside (7/20) (-7/20)
  near : E.Inside (13/50) (-1)
  outer : E.Inside (2/5) (-1)
  halfpoint : E.Inside (1/2) (-1)
  missingInner : ¬E.Inside 0 (-13/50)
  missingRight : ¬E.Inside 1 (-2/5)
  missingBottom : ¬E.Inside 0 (-543/500)
  missingCorner : ¬E.Inside 1 (-1)
  missingCornerMarker : ¬E.Inside 1 (-543/500)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

theorem nonnegative_successor_faces (C E : OpenSquare) (h : SignInput C E)
    (en : Normal E.c E.s) :
    E.loU+E.side≤E.c-(2/5)*E.s ∧ E.loV+E.side≤-(13/50)*E.c ∧
      -E.c-E.s≤E.loV := by
  exact NonnegativeRecipient.faces E
    ⟨by simpa only [←h.same] using h.side,h.successorMarker,h.near,h.outer,
      h.missingInner,h.missingRight,h.missingBottom,h.missingCorner,h.missingCornerMarker⟩ en

private theorem sign_axes (C E : OpenSquare) (h : SignInput C E)
    (en : Normal E.c E.s) :
    C.loU+C.side≤lower E C.c C.s ∨
      upper C E.c E.s≤E.loU ∨ upper C E.s (-E.c)≤-(E.loV+E.side) := by
  have cb := normal_bounds h.central
  have eb := normal_bounds en
  have cp : 0<C.c := by linarith only [cb.1]
  have ep : 0<E.c := by linarith only [eb.1]
  have rightward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx := by
    have first := (strict_bounds C _ _ nx ny unit h.marker).2
    have last := (strict_bounds E _ _ nx ny unit h.successorMarker).1
    linarith only [first,last,sep]
  have downward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx-ny := by
    have first := (strict_bounds C _ _ nx ny unit h.crosspoint).2
    have last := (strict_bounds E _ _ nx ny unit h.halfpoint).1
    linarith only [first,last,sep]
  have axes := CongruentSAT.faceSeparation_of_disjoint C E h.same h.apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius E nx ny=radius)
      (sep : radius≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [eq])
  rcases axes with cu|cv|eu|ev
  · rcases split _ _ _ (parallel_radius C E) cu with direct|back
    · exact Or.inl (by simpa only [(ownU C).2] using direct)
    · have no := rightward (-C.c) (-C.s) (by nlinarith only [C.unit_normal]) (reverse C E _ _ back)
      exact False.elim (by linarith only [no,cp])
  · rcases split _ _ _ (transverse_radius C E) cv with direct|back
    · have no := downward (-C.s) C.c (by nlinarith only [C.unit_normal]) direct
      exact False.elim (by linarith only [no,h.central.2.1])
    · have no := rightward C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse C E _ _ back)
      exact False.elim (by linarith only [no,h.central.1])
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases split _ _ _ radius eu with direct|back
    · exact Or.inr (Or.inl (by simpa only [(ownU E).1] using direct))
    · have no := rightward (-E.c) (-E.s) (by nlinarith only [E.unit_normal]) (reverse C E _ _ back)
      exact False.elim (by linarith only [no,ep])
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases split _ _ _ radius ev with direct|back
    · have no := rightward (-E.s) E.c (by nlinarith only [E.unit_normal]) direct
      exact False.elim (by linarith only [no,en.1])
    · have formula : lower E E.s (-E.c)=-(E.loV+E.side) := by
        have neg := lower_neg E (-E.s) E.c
        simpa only [neg_neg,(ownV E).2] using neg
      right; right
      simpa only [neg_neg,formula] using reverse C E _ _ back

theorem nonnegative_successor_impossible (C E : OpenSquare) (h : SignInput C E)
    (en : Normal E.c E.s) : False := by
  have faces := nonnegative_successor_faces C E h en
  have cb := normal_bounds h.central
  have eb := normal_bounds en
  have cp : 0<C.c := by linarith only [cb.1]
  have ep : 0<E.c := by linarith only [eb.1]
  have tp : 0<E.s := by linarith only [faces.2.1,faces.2.2,h.side,h.same,eb.2.1]
  let k := C.c*E.c+C.s*E.s
  let j := C.c*E.s-C.s*E.c
  have kn : 0≤k := by
    have first := mul_nonneg (show 0≤C.c+C.s by linarith only [h.central.2.1]) ep.le
    have last := mul_nonneg h.central.1 (sub_nonneg.mpr en.2.1)
    dsimp [k]; nlinarith only [first,last]
  have jn : 0≤j := by
    have first := mul_nonneg cp.le en.1
    have last := mul_nonneg h.central.1 ep.le
    dsimp [j]; nlinarith only [first,last]
  have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k+j by linarith only [kn,jn])
  rcases sign_axes C E h en with own|eu|ev
  · have formula := lower_pn E C.c C.s k (-j)
      (by dsimp [k]; ring) (by dsimp [j]; ring) kn (by linarith only [jn])
    have first := mul_nonneg kn
      (show 0≤E.c-(2/5)*E.s-C.side-E.loU by linarith only [faces.1,h.same])
    have last := mul_nonneg jn (show 0≤E.loV+E.c+E.s by linarith only [faces.2.2])
    have margin := sign_first_positive h.central en tp
    dsimp [signFirst,k,j] at formula first last strict margin
    nlinarith only [own,formula,first,last,strict,margin,h.lowerA,h.same]
  · have inner := (strict_bounds C _ _ E.c E.s E.unit_normal h.inner).2
    nlinarith only [eu,inner,faces.1,h.side,h.same,eb.2.1,en.1]
  · have formula := upper_pos_neg C E.s (-E.c) j (-k)
      (by dsimp [j]; ring) (by dsimp [k]; ring) jn (by linarith only [kn])
    have first := mul_nonneg jn
      (show 0≤C.loU+C.c+(13/50)*C.s by linarith only [h.lowerA])
    have last := mul_nonneg kn
      (show 0≤(7/20)*(C.c+C.s)-C.loV-C.side by linarith only [h.upperH])
    have margin := sign_last_positive h.central en
    dsimp [signLast,k,j] at formula first last strict margin
    nlinarith only [ev,formula,first,last,strict,margin,faces.2.2,h.same]

theorem successor_negative (C E : OpenSquare) (h : SignInput C E)
    (canonical : |E.s|≤E.c) : E.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  have en : Normal E.c E.s := ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using canonical,E.unit_normal⟩
  exact nonnegative_successor_impossible C E h en

#print axioms nonnegative_successor_faces
#print axioms successor_negative
end N12Compact.C1092MPPMInwardFinal
