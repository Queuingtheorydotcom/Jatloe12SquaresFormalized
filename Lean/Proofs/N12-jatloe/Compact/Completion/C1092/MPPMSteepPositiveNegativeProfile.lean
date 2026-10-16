import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfileScalars
import Compact.Completion.C1092.MPPMNonpositivePredecessor
import Compact.Completion.C1092.TwoFifthsSupport

/-! Full actual-square STEEP-POSITIVE-NEGATIVE-PROFILE Theorem 1.
The successor faces and strict shallow angle are derived from its literal
ordinary/forward points and the two genuine omissions. All three signed
separating sources, including aligned and diagonal contacts, are covered.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMSteepPositiveNegativeProfile
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092TwoFifths.Support Scalars
set_option Elab.async false
noncomputable section

structure Input (C E : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  central : Normal C.c C.s
  steep : 3/5≤C.s
  recipient : Normal E.c (-E.s)
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-C.c/2
  upperV : C.loV+C.side≤C.s
  markerC : C.Inside (-7/20) (-7/20)
  ordinaryC : C.Inside (-1) (-13/50)
  markerE : E.Inside (7/20) (-7/20)
  bottom0 : E.Inside (13/50) (-1)
  bottom1 : E.Inside (2/5) (-1)
  forwardE : E.Inside 0 (-13/50)
  originE : ¬E.Inside 0 (-1)
  cornerE : ¬E.Inside 1 (-1)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

structure Faces (E : OpenSquare) : Prop where
  positive : 0< -E.s
  shallow : (-E.s)/E.c<3/8
  lowerV : -E.c≤E.loV
  upperU : E.loU+E.side≤E.c-E.s
  strictU : E.loU< -(13/50)*E.s
  strictV : E.loV< -(13/50)*E.s-E.c
  lowerU : -(7/20)*(E.c+E.s)≤E.loU

/-- The two genuine omissions select opposite actual faces. The strict
ordinary anchor then excludes the axial successor representative. -/
private theorem initial_faces (C E : OpenSquare) (h : Input C E) :
    -E.c≤E.loV ∧ E.loU+E.side≤E.c-E.s ∧ 0< -E.s := by
  have eb := normal_bounds h.recipient
  have dp : 0<E.c := by linarith only [eb.1]
  have sn : E.s≤0 := by linarith only [h.recipient.1]
  have lowerV : -E.c≤E.loV := by
    apply le_of_not_gt
    intro low
    apply h.originE
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.forwardE.1,h.bottom0.2.1,h.forwardE.2.2.2,dp,sn]
  have upperU : E.loU+E.side≤E.c-E.s := by
    apply le_of_not_gt
    intro high
    apply h.cornerE
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.markerE.1,h.bottom0.2.2.1,h.markerE.2.2.2,
        dp,sn,h.recipient.2.1]
  exact ⟨lowerV,upperU,by linarith only [lowerV,h.bottom0.2.2.1]⟩

private theorem recipient_axis (C E : OpenSquare) (h : Input C E)
    (low : -E.c≤E.loV) (high : E.loU+E.side≤E.c-E.s) :
    upper C E.c E.s≤E.loU := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.central).1]
  have dp : 0<E.c := by linarith only [(normal_bounds h.recipient).1]
  have sp : 0<C.s := by linarith only [h.steep]
  have cf : C1092MPPMOrdinaryNegativeHalfpoint.Frame C.c C.s :=
    ⟨cp,h.central.1,h.central.2.1,h.central.2.2⟩
  have ef : C1092MPPMOrdinaryNegativeHalfpoint.Frame E.c (-E.s) :=
    ⟨dp,h.recipient.1,h.recipient.2.1,h.recipient.2.2⟩
  let k := C.c*E.c+C.s*E.s
  let ell := -C.c*E.s+C.s*E.c
  have relative := C1092MPPMNonpositivePredecessor.relative C.c C.s E.c (-E.s) cf ef
  have kn : 0≤k := by dsimp [k]; nlinarith only [relative.1]
  have ln : 0<ell := by
    have first := mul_nonneg cp.le h.recipient.1
    have last := mul_pos sp dp
    dsimp [ell]
    nlinarith only [first,last]
  rcases C1092MPPMNonpositivePredecessor.positive_axes C E h.same cf ef
      h.markerC h.markerE h.bottom0 h.apart with current|transverse|recipient
  · have formula := lower_nn E C.c C.s k ell
      (by dsimp [k]) (by dsimp [ell]) kn ln.le
    have first := mul_le_mul_of_nonneg_left high kn
    have last := mul_le_mul_of_nonneg_left h.bottom0.2.2.1.le ln.le
    rw [←h.same] at first
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k by linarith only [kn])
    have margin := current_margin h.central h.recipient
    have identity : (C.side-C.c-C.s)-k*(E.c-E.s-C.side)-
        ell*(-(13/50)*E.s-E.c)=
        1-Pu E.c (-E.s)*C.c-Qu E.c (-E.s)*C.s+(C.side-1)*(1+k) := by
      dsimp [k,ell,Pu,Qu]
      linear_combination (C.s-C.c)*E.unit_normal
    have source : C.side-C.c-C.s≤C.loU+C.side := by linarith only [h.lowerU]
    exact False.elim (by nlinarith only [formula,first,last,strict,margin,identity,source,current])
  · have formula := lower_pn E C.s (-C.c) ell (-k)
      (by dsimp [ell]; ring) (by dsimp [k]; ring) ln.le (neg_nonpos.mpr kn)
    have first := mul_le_mul_of_nonneg_left h.forwardE.1.le ln.le
    have last := mul_le_mul_of_nonneg_left low kn
    rw [←h.same] at formula
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k by linarith only [kn])
    have margin := transverse_margin h.central h.recipient
    have identity : C.side-C.s-ell*(-(13/50)*E.s)+k*(C.side-E.c)=
        1-Pv E.c*C.c-Qv E.c (-E.s)*C.s+(C.side-1)*(1+k) := by
      dsimp [k,ell,Pv,Qv]
      linear_combination -(13/50)*C.c*E.unit_normal
    exact False.elim (by
      nlinarith only [formula,first,last,strict,margin,identity,h.upperV,transverse])
  · exact recipient

/-- The complete negative successor profile is a conclusion, not an
input to the actual three-square transfer which follows this chapter. -/
theorem profile (C E : OpenSquare) (h : Input C E) : Faces E := by
  have initial := initial_faces C E h
  have separator := recipient_axis C E h initial.1 initial.2.1
  have cb := normal_bounds h.central
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [cb.1]
  have dp : 0<E.c := by linarith only [eb.1]
  let k := C.c*E.c+C.s*E.s
  let ell := -C.c*E.s+C.s*E.c
  have first := mul_nonneg (sub_nonneg.mpr h.central.2.1) dp.le
  have last := mul_nonneg h.central.1
    (show 0≤E.c+E.s by linarith only [h.recipient.2.1])
  have kn : 0≤k := by dsimp [k]; nlinarith only [first,last]
  have ln : 0<ell := by
    have first := mul_nonneg cp.le h.recipient.1
    have last := mul_pos (show 0<C.s by linarith only [h.steep]) dp
    dsimp [ell]
    nlinarith only [first,last]
  have shallow : (-E.s)/E.c<3/8 := by
    apply lt_of_not_ge
    intro large
    have slope := (le_div_iff₀ dp).mp large
    have formula := upper_pos_neg C E.c E.s k (-ell)
      (by dsimp [k]; ring) (by dsimp [ell]; ring) kn (by linarith only [ln])
    have lower := mul_le_mul_of_nonneg_left h.lowerU kn
    have upper := mul_le_mul_of_nonneg_left h.upperV ln.le
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<k+ell by linarith only [kn,ln])
    have envelope := envelope h.central
    have fweight := mul_lt_mul_of_pos_left envelope.1 dp
    have bweight := mul_le_mul_of_nonneg_left envelope.2 h.recipient.1
    have margin : 0< -E.c*f C.c C.s+(-E.s)*B C.c C.s := by
      nlinarith only [fweight,bweight,slope,dp]
    have identity : k*(C.side-C.c-C.s)-ell*(C.s-C.side)+(13/50)*E.s=
        -E.c*f C.c C.s+(-E.s)*B C.c C.s+(C.side-1)*(k+ell) := by
      dsimp [k,ell,f,B]
      linear_combination -E.c*C.unit_normal
    exact False.elim (by
      nlinarith only [formula,lower,upper,strict,margin,identity,h.forwardE.1,separator])
  have lowerU : -(7/20)*(E.c+E.s)≤E.loU := by
    apply le_of_not_gt
    intro low
    apply h.apart (-7/20) (-7/20)
    refine ⟨h.markerC,?_,?_,?_,?_⟩ <;>
      linarith only [low,h.markerE.2.1,h.bottom0.2.2.1,h.forwardE.2.2.2,
        dp,h.recipient.1,h.recipient.2.1]
  exact ⟨initial.2.2,shallow,initial.1,initial.2.1,
    by linarith only [h.forwardE.1],by linarith only [h.bottom0.2.2.1],lowerU⟩

end
#print axioms profile
end N12Compact.C1092MPPMSteepPositiveNegativeProfile
