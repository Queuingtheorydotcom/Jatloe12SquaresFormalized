import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry
import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfile
import Compact.Completion.C1092.MPPMNegativeCrosspointSupportScalars

/-! Actual signed sources and simultaneous support caps for
STEEP-POSITIVE-NEGATIVE-CROSSPOINT-TRANSFER §§1--3. The negative
recipient's full profile is produced from its literal two-square inputs.
One physical boundary square retains its marker, outer point and origin.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeCrosspointGeometry
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092TwoFifths.Support C1092MPPMNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

structure Input (C E B : OpenSquare) : Prop where
  central : C1092MPPMSteepPositiveNegativeProfile.Input C E
  sameB : C.side=B.side
  markerB : B.Inside 0 (-543/500)
  outerB : B.Inside (-2/5) (-1)
  originB : B.Inside 0 (-1)
  wall : ∀ x y,B.Inside x y→-2≤y
  apartC : ∀ x y,¬(B.Inside x y ∧ C.Inside x y)
  apartE : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)

theorem central_sources (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    upper B (-C.s) C.c≤C.loV ∨ upper B (-B.s) B.c≤lower C (-B.s) B.c := by
  have cb := normal_bounds h.central.central
  have cone := C1092MPPMSteepPositiveThreeSquare.anchor_cone C B
    h.central.markerC h.central.ordinaryC h.markerB h.outerB
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B C h.sameB.symm h.apartC
      with a|b|c|d|e|f|g|j
  · have upperV : C.loV+C.side≤(543/500)*C.s := by
      linarith only [h.central.upperV,h.central.central.1]
    exact False.elim (C1092MPPMSteepPositiveThreeSquare.northeast_of_faces C B
      h.central.side h.central.central (by linarith only [h.central.steep])
      h.central.upperU upperV h.central.markerC h.central.ordinaryC h.markerB h.outerB
      _ _ B.unit_normal bn.cosine bn.sine a)
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) b).1
    exact False.elim (by linarith only [no,bn.sine])
  · exact Or.inr c
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) d).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ C.unit_normal e).2
    exact False.elim (by linarith only [no,h.central.central.2.1,cb.1])
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) f).1
    exact False.elim (by linarith only [no,h.central.central.1])
  · exact Or.inl (by simpa only [(ownV C).1] using g)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) j).1
    exact False.elim (by linarith only [no,cb.1])

theorem recipient_sources (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    upper B (-E.s) E.c≤E.loV ∨ upper B B.c B.s≤lower E B.c B.s := by
  have eb := normal_bounds h.central.recipient
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower E nx ny) : 0<nx ∧ 0<ny := by
    have first := (strict_bounds E _ _ nx ny unit h.central.bottom1).1
    have last := (strict_bounds E _ _ nx ny unit h.central.forwardE).1
    have origin := (strict_bounds B _ _ nx ny unit h.originB).2
    constructor <;> linarith only [first,last,origin,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B E
      (h.sameB.symm.trans h.central.same) h.apartE with a|b|c|d|e|f|g|j
  · exact Or.inr a
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) b).1
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) c).1
    exact False.elim (by linarith only [no,bn.sine])
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) d).2
    exact False.elim (by linarith only [no,bn.cosine])
  · have no := (cone _ _ E.unit_normal e).2
    exact False.elim (by linarith only [no,h.central.recipient.1])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) f).1
    exact False.elim (by linarith only [no,eb.1])
  · exact Or.inl (by simpa only [(ownV E).1] using g)
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) j).2
    exact False.elim (by linarith only [no,eb.1])

theorem central_dot (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    0≤kC C.c C.s B.c B.s := by
  have cp : 0≤C.c := by linarith only [(normal_bounds h.central.central).1]
  exact add_nonneg (mul_nonneg cp bn.cosine) (mul_nonneg h.central.central.1 bn.sine)

theorem recipient_dot (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    0≤kE E.c (-E.s) B.c B.s := by
  have dp : 0≤E.c := by linarith only [(normal_bounds h.central.recipient).1]
  exact add_nonneg (mul_nonneg h.central.recipient.1 bn.cosine) (mul_nonneg dp bn.sine)

theorem central_cap (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    lower C (-B.s) B.c≤FC C.c C.s B.c B.s-
      (C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|) := by
  have kn := central_dot C E B h bn
  have du : (-B.s)*C.c+B.c*C.s= -deltaC C.c C.s B.c B.s := by dsimp [deltaC]; ring
  have dv : -(-B.s)*C.s+B.c*C.c=kC C.c C.s B.c B.s := by dsimp [kC]; ring
  have upper := mul_le_mul_of_nonneg_left h.central.upperV kn
  by_cases order : 0≤deltaC C.c C.s B.c B.s
  · have formula := lower_np C (-B.s) B.c _ _ du dv (neg_nonpos.mpr order) kn
    have lower := mul_le_mul_of_nonneg_left h.central.lowerU order
    rw [FC,if_pos order,abs_of_nonneg order]
    nlinarith only [formula,lower,upper]
  · have order' := (lt_of_not_ge order).le
    have formula := lower_nn C (-B.s) B.c _ _ du dv (neg_nonneg.mpr order') kn
    have face := mul_le_mul_of_nonneg_left h.central.upperU (neg_nonneg.mpr order')
    rw [FC,if_neg order,abs_of_nonpos order']
    nlinarith only [formula,face,upper]

/-- Both signed uses of E's actual first face retain the same lower
face L and upper face J=L+a. The side correction is precisely max(deltaE,0). -/
theorem recipient_cap (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    lower E B.c B.s≤FE E.c (-E.s) B.c B.s-
      (C.side-1)*max (deltaE E.c (-E.s) B.c B.s) 0 := by
  have faces := C1092MPPMSteepPositiveNegativeProfile.profile C E h.central
  have kn := recipient_dot C E B h bn
  have du : B.c*E.c+B.s*E.s= -deltaE E.c (-E.s) B.c B.s := by dsimp [deltaE]; ring
  have dv : -B.c*E.s+B.s*E.c=kE E.c (-E.s) B.c B.s := by dsimp [kE]; ring
  have upper := mul_le_mul_of_nonneg_left faces.strictV.le kn
  by_cases order : 0≤deltaE E.c (-E.s) B.c B.s
  · have formula := lower_np E B.c B.s _ _ du dv (neg_nonpos.mpr order) kn
    have lower := mul_le_mul_of_nonneg_left faces.lowerU order
    have form : FE E.c (-E.s) B.c B.s=
        -deltaE E.c (-E.s) B.c B.s*(1-(7/20)*(E.c+E.s))+
          kE E.c (-E.s) B.c B.s*E0 E.c (-E.s) := by
      rw [FE,if_pos order]
      dsimp [P2,Q2,deltaE,kE,E0]
      linear_combination ((7/20)*B.c+B.s)*E.unit_normal
    rw [←h.central.same] at formula
    rw [form,max_eq_left order]
    dsimp [E0]
    nlinarith only [formula,lower,upper]
  · have order' := (lt_of_not_ge order).le
    have formula := lower_nn E B.c B.s _ _ du dv (neg_nonneg.mpr order') kn
    have lower := mul_le_mul_of_nonneg_left faces.strictU.le (neg_nonneg.mpr order')
    have form : FE E.c (-E.s) B.c B.s=
        -deltaE E.c (-E.s) B.c B.s*(-(13/50)*E.s)+
          kE E.c (-E.s) B.c B.s*E0 E.c (-E.s) := by
      rw [FE,if_neg order]
      dsimp [P,Q,deltaE,kE,E0]
      linear_combination B.s*E.unit_normal
    rw [form,max_eq_right order']
    dsimp [E0]
    nlinarith only [formula,lower,upper]

/-- An E-separating actual boundary normal must lie strictly above the
coordinate diagonal. Below it, the actual origin already blocks it. -/
theorem boundary_recipient_high (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) (sep : upper B B.c B.s≤lower E B.c B.s) : B.c<B.s := by
  apply lt_of_not_ge
  intro low
  have faces := C1092MPPMSteepPositiveNegativeProfile.profile C E h.central
  have eb := normal_bounds h.central.recipient
  have kn := recipient_dot C E B h bn
  have first := mul_nonneg h.central.recipient.1 (sub_nonneg.mpr low)
  have last := mul_nonneg bn.cosine
    (show 0≤E.c+E.s by linarith only [h.central.recipient.2.1])
  have order : deltaE E.c (-E.s) B.c B.s≤0 := by
    dsimp [deltaE]
    nlinarith only [first,last]
  have formula := lower_nn E B.c B.s _ _
    (show B.c*E.c+B.s*E.s= -deltaE E.c (-E.s) B.c B.s by dsimp [deltaE]; ring)
    (show -B.c*E.s+B.s*E.c=kE E.c (-E.s) B.c B.s by dsimp [kE]; ring)
    (neg_nonneg.mpr order) kn
  have a := mul_le_mul_of_nonneg_left faces.strictU.le (neg_nonneg.mpr order)
  have b := mul_le_mul_of_nonneg_left faces.strictV.le kn
  have form : -P E.c (-E.s)*B.c-Q E.c (-E.s)*B.s=
      -deltaE E.c (-E.s) B.c B.s*(-(13/50)*E.s)+
        kE E.c (-E.s) B.c B.s*E0 E.c (-E.s) := by
    dsimp [P,Q,deltaE,kE,E0]
    linear_combination B.s*E.unit_normal
  have pn : 0≤P E.c (-E.s) := by
    have weight := mul_nonneg h.central.recipient.1
      (show 0≤(37/50)*E.c+(13/50)*E.s by linarith only [h.central.recipient.2.1,eb.1])
    dsimp [P]
    nlinarith only [weight]
  have slope := (div_lt_iff₀ (show 0<E.c by linarith only [eb.1])).mp faces.shallow
  have pq : 0≤P E.c (-E.s)+Q E.c (-E.s)-1 := by
    have weight := mul_nonneg h.central.recipient.1
      (show 0≤(12/25)*E.c+E.s by linarith only [slope,eb.1])
    dsimp [P,Q]
    nlinarith only [weight]
  have c := mul_nonneg pn (sub_nonneg.mpr low)
  have d := mul_nonneg pq bn.sine
  have origin := (strict_bounds B _ _ B.c B.s B.unit_normal h.originB).2
  dsimp [E0] at form
  nlinarith only [formula,a,b,form,c,d,origin,sep]

end
#print axioms central_sources
#print axioms recipient_sources
#print axioms recipient_cap
#print axioms boundary_recipient_high
end N12Compact.C1092MPPMNegativeCrosspointGeometry
