import Compact.Completion.C1092.MPPMMissingNegativeCrosspointFaces
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry

/-! Complete actual normal cones for the missing-negative successor
three-square theorem. Its downward boundary sources are excluded using
the genuine successor faces, not by discarding a boundary-center term.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092MPPMMissingNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

structure Input (C E B : OpenSquare) : Prop where
  side : 1<C.side
  sameE : C.side=E.side
  sameB : C.side=B.side
  central : Normal C.c C.s
  steep : 3/5≤C.s
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-C.c/2
  upperV : C.loV+C.side≤(543/500)*C.s
  markerC : C.Inside (-7/20) (-7/20)
  ordinaryC : C.Inside (-1) (-13/50)
  recipient : RecipientInput E B
  markerB : B.Inside 0 (-543/500)
  outerB : B.Inside (-2/5) (-1)
  wall : ∀ x y,B.Inside x y→-2≤y
  apartC : ∀ x y,¬(B.Inside x y ∧ C.Inside x y)

theorem central_sources (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    upper B (-C.s) C.c≤C.loV ∨ upper B (-B.s) B.c≤lower C (-B.s) B.c := by
  have cb := normal_bounds h.central
  have cone := C1092MPPMSteepPositiveThreeSquare.anchor_cone C B
    h.markerC h.ordinaryC h.markerB h.outerB
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B C h.sameB.symm h.apartC
      with a|b|c|d|e|f|g|j
  · exact False.elim (C1092MPPMSteepPositiveThreeSquare.northeast_of_faces C B h.side h.central
      (by linarith only [h.steep]) h.upperU h.upperV h.markerC h.ordinaryC h.markerB h.outerB
      _ _ B.unit_normal bn.cosine bn.sine a)
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) b).1
    exact False.elim (by linarith only [no,bn.sine])
  · exact Or.inr c
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) d).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ C.unit_normal e).2
    exact False.elim (by linarith only [no,h.central.2.1,cb.1])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) f).1
    exact False.elim (by linarith only [no,h.central.1])
  · exact Or.inl (by simpa only [(ownV C).1] using g)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) j).1
    exact False.elim (by linarith only [no,cb.1])

theorem recipient_cone (C E B : OpenSquare) (h : Input C E B)
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (sep : upper B nx ny≤lower E nx ny) :
    0<nx ∧ 0<(7/20)*nx+(13/20)*ny := by
  have first := (strict_bounds E _ _ nx ny unit h.recipient.ordinaryG).1
  have last := (strict_bounds E _ _ nx ny unit h.recipient.marker).1
  have origin := (strict_bounds B _ _ nx ny unit h.recipient.originB).2
  constructor <;> linarith only [first,last,origin,sep]

/-- A downward B face would put E below its actual strict B-owned
origin. The positive longitudinal/transverse coefficients are forced by
the real anchor cone and the derived large successor sine. -/
theorem downward_impossible (C E B : OpenSquare) (h : Input C E B)
    (xi eta : ℝ) (xn : 0<xi) (yn : 0≤eta) (unit : xi^2+(-eta)^2=1) :
    ¬upper B xi (-eta)≤lower E xi (-eta) := by
  intro sep
  have cone := recipient_cone C E B h xi (-eta) unit sep
  have f := recipient_faces E B h.recipient
  have eb := normal_bounds h.recipient.normal
  have dp : 0<E.c := by linarith only [eb.1]
  have tp : 0< -E.s := by linarith only [f.negative]
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order h.recipient.normal endpoint f.large
  let alpha := E.c*xi-E.s*eta
  let mu := -E.s*xi-E.c*eta
  have ap : 0<alpha := by
    have first := mul_pos dp xn
    have last := mul_nonneg tp.le yn
    dsimp [alpha]
    nlinarith only [first,last]
  have mp : 0<mu := by
    have first := mul_nonneg (show 0≤-E.s-252/373 by linarith only [f.large]) xn.le
    have last := mul_nonneg (show 0≤1-E.c by linarith only [eb.2.1]) yn
    dsimp [mu]
    nlinarith only [first,last,cone.2,xn]
  have formula := lower_nn E xi (-eta) alpha mu
    (by dsimp [alpha]; ring) (by dsimp [mu]; ring) ap.le mp.le
  have first := mul_le_mul_of_nonneg_left f.upperU ap.le
  have last := mul_le_mul_of_nonneg_left f.upperV mp.le
  rw [←h.sameE] at first last
  have strict := mul_pos (sub_pos.mpr h.side) (show 0<alpha+mu by linarith only [ap,mp])
  let a := 1-E.c+E.s-(11/25)*E.c*E.s
  let b := -E.s-E.c-14/25-(11/25)*E.s^2
  have dot : E.c*(-E.s)≤1/2 := by
    nlinarith only [E.unit_normal,sq_nonneg (E.c+E.s)]
  have ordered := mul_nonneg
    (show 0≤E.c+E.s by linarith only [h.recipient.normal.2.1])
    (show 0≤E.c-E.s by linarith only [dp,tp])
  have small : E.s^2≤1/2 := by nlinarith only [ordered,E.unit_normal]
  have an : a<0 := by dsimp [a]; nlinarith only [eb.1,f.large,dot]
  have bp : 0<1+b := by dsimp [b]; nlinarith only [cosine,f.large,small]
  have negative := mul_neg_of_pos_of_neg xn an
  have positive := mul_nonneg bp.le yn
  have identity : alpha*(E.c-E.s-1)+mu*(-E.s-(14/25)*E.c-1)-eta=
      a*xi-(1+b)*eta := by
    dsimp [alpha,mu,a,b]
    linear_combination (xi+(14/25)*eta)*E.unit_normal
  have origin := (strict_bounds B _ _ xi (-eta) unit h.recipient.originB).2
  nlinarith only [formula,first,last,strict,negative,positive,identity,origin,sep]

theorem recipient_sources (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    upper B (-E.s) E.c≤E.loV ∨ upper B B.c B.s≤lower E B.c B.s := by
  have f := recipient_faces E B h.recipient
  have eb := normal_bounds h.recipient.normal
  have cone := recipient_cone C E B h
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B E
      (h.sameB.symm.trans h.sameE) h.recipient.apart with a|b|c|d|e|j|k|l
  · exact Or.inr a
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) b).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) c).1
    exact False.elim (by linarith only [no,bn.sine])
  · exact False.elim (downward_impossible C E B h B.s B.c
      (cone _ _ (by nlinarith only [B.unit_normal]) d).1 bn.cosine
      (by nlinarith only [B.unit_normal]) d)
  · have no := (cone _ _ E.unit_normal e).2
    exact False.elim (by linarith only [no,eb.2.1,f.large])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) j).1
    exact False.elim (by linarith only [no,eb.1])
  · exact Or.inl (by simpa only [(ownV E).1] using k)
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) l).1
    exact False.elim (by linarith only [no,f.negative])

theorem central_dot (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    0≤kC C.c C.s B.c B.s := by
  have cp : 0≤C.c := by linarith only [(normal_bounds h.central).1]
  exact add_nonneg (mul_nonneg cp bn.cosine) (mul_nonneg h.central.1 bn.sine)

theorem recipient_dot (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    0≤kE E.c (-E.s) B.c B.s := by
  have dp : 0≤E.c := by linarith only [(normal_bounds h.recipient.normal).1]
  exact add_nonneg (mul_nonneg h.recipient.normal.1 bn.cosine) (mul_nonneg dp bn.sine)

/-- The unconditional positive face contributes precisely the printed
epsilon allowance. Both signs use the same actual C faces. -/
theorem central_cap (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    lower C (-B.s) B.c≤FC C.c C.s B.c B.s+(43/500)*C.s*kC C.c C.s B.c B.s-
      (C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|) := by
  have kn := central_dot C E B h bn
  have du : (-B.s)*C.c+B.c*C.s= -deltaC C.c C.s B.c B.s := by
    dsimp [deltaC, C1092MPPMNegativeCrosspointSupport.deltaC]; ring
  have dv : -(-B.s)*C.s+B.c*C.c=kC C.c C.s B.c B.s := by
    dsimp [kC, C1092MPPMNegativeCrosspointSupport.kC]; ring
  have upper := mul_le_mul_of_nonneg_left h.upperV kn
  by_cases order : 0≤deltaC C.c C.s B.c B.s
  · have formula := lower_np C (-B.s) B.c _ _ du dv (neg_nonpos.mpr order) kn
    have lower := mul_le_mul_of_nonneg_left h.lowerU order
    rw [FC,C1092MPPMNegativeCrosspointSupport.FC,ite_eq_left order,abs_of_nonneg order]
    nlinarith only [formula,lower,upper]
  · have order' := (lt_of_not_ge order).le
    have formula := lower_nn C (-B.s) B.c _ _ du dv (neg_nonneg.mpr order') kn
    have face := mul_le_mul_of_nonneg_left h.upperU (neg_nonneg.mpr order')
    rw [FC,C1092MPPMNegativeCrosspointSupport.FC,ite_eq_right order,abs_of_nonpos order']
    nlinarith only [formula,face,upper]

/-- The missing successor supplies a full side correction on both
actual axes. Its lower first face is used only with the negative
longitudinal coefficient; its upper first face is used with the positive
coefficient, including the shared zero-coefficient contact. -/
theorem recipient_cap (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    lower E B.c B.s≤FE E.c (-E.s) B.c B.s-
      (C.side-1)*(kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|) := by
  have faces := recipient_faces E B h.recipient
  have kn := recipient_dot C E B h bn
  have du : B.c*E.c+B.s*E.s= -deltaE E.c (-E.s) B.c B.s := by
    dsimp [deltaE, C1092MPPMNegativeCrosspointSupport.deltaE]; ring
  have dv : -B.c*E.s+B.s*E.c=kE E.c (-E.s) B.c B.s := by
    dsimp [kE, C1092MPPMNegativeCrosspointSupport.kE]; ring
  have upper := mul_le_mul_of_nonneg_left faces.upperV kn
  by_cases order : 0≤deltaE E.c (-E.s) B.c B.s
  · have formula := lower_np E B.c B.s _ _ du dv (neg_nonpos.mpr order) kn
    have lower := mul_le_mul_of_nonneg_left faces.lowerU order
    rw [←h.sameE] at upper formula
    rw [FE,ite_eq_left order,abs_of_nonneg order]
    dsimp [E0]
    nlinarith only [formula,lower,upper]
  · have order' := (lt_of_not_ge order).le
    have formula := lower_nn E B.c B.s _ _ du dv (neg_nonneg.mpr order') kn
    have first := mul_le_mul_of_nonneg_left faces.upperU (neg_nonneg.mpr order')
    rw [←h.sameE] at upper first
    rw [FE,ite_eq_right order,abs_of_nonpos order']
    dsimp [E0]
    nlinarith only [formula,first,upper]

end
#print axioms downward_impossible
#print axioms recipient_sources
#print axioms central_cap
#print axioms recipient_cap
end N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
