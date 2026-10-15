import Compact.Completion.C1092.MPPMCenteredPositiveData
import Compact.Completion.C1092.MPPMInwardFinalCenteredCaps
import Compact.Completion.C1092.MPPMInwardFinalBottomScalars

/-! CENTERED-POSITIVE-INWARD §§3--5. The actual southeast normal
comparison supplies the full G face, the shallow angle, the strict
height lower bound and the narrow A cap of the same C. -/
namespace N12Compact.C1092MPPMCenteredPositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WallProfileScalars C1092MPPMInwardFinal
open C1092MPPMOrdinaryNegativeHalfpoint C1092MPPMPositiveOverlap
set_option Elab.async false

theorem successor_profile (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c C.s) (ep : 0<E.c) (canonical : |E.s|≤E.c)
    (h : Input C E) : E.s<0 ∧ NegativeSuccessor E ∧
      99/100<C.c ∧ C.s<7/50 ∧
      1+(C.c*(-E.s)+C.s*E.c)<E.c-E.s+(C.c*(-E.s)+C.s*E.c)*(C.loV+C.side) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have cf : C1092MPPMOrdinaryNegativeHalfpoint.Frame C.c C.s := ⟨cp,cn.1,cn.2.1,cn.2.2⟩
  have caps := center_caps C E side cn h
  have negative := successor_negative C E side same cn canonical h
  have en : Normal E.c (-E.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,by nlinarith only [E.unit_normal]⟩
  have ef : C1092MPPMOrdinaryNegativeHalfpoint.Frame E.c (-E.s) := ⟨ep,en.1,en.2.1,en.2.2⟩
  have ef0 := successor_faces C E (by rwa [←same]) en h
  let c := C.c
  let s := C.s
  let d := E.c
  let t := -E.s
  let k := c*d-s*t
  let j := c*t+s*d
  have kn : 0≤k := (C1092MPPMNonpositivePredecessor.relative c s d t cf ef).1
  have jp : 0<j := by
    have first := mul_pos cp (show 0<t by dsimp [t]; linarith only [negative])
    have second := mul_nonneg cn.1 ep.le
    dsimp [j,c,s,d] at first second ⊢
    linarith only [first,second]
  have ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  have ownK := mul_nonneg kn ap.le
  have lowSupport : lower E C.c C.s=k*E.loU+j*E.loV :=
    C1092WholeSupports.lower_nn E C.c C.s k j
      (by dsimp [k,c,s,d,t]; ring) (by dsimp [j,c,s,d,t]; ring) kn jp.le
  have ku : E.c*C.c+E.s*C.s=k := by dsimp [k,c,s,d,t]; ring
  have jv : -E.c*C.s+E.s*C.c= -j := by dsimp [j,c,s,d,t]; ring
  have highSupport : upper C E.c E.s=k*(C.loU+C.side)-j*C.loV := by
    rw [(C1092WholeSupports.formulas C E.c E.s).2,ku,jv,
      max_eq_left kn,max_eq_right (neg_nonpos.mpr jp.le)]
    ring
  have axes : C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
    rcases C1092MPPMNonpositivePredecessor.positive_axes C E same cf ef
        h.marker h.successorMarker h.near h.apart with cu | cv | eu
    · exact Or.inl cu
    · have strict := (strict_bounds E _ _ C.s (-C.c)
        (by nlinarith only [C.unit_normal]) h.successorMarker).1
      linarith only [cv,strict,caps.2,side,cb.2.2.2.2.2]
    · exact Or.inr eu
  have weakV : E.loV+C.side≤t := by dsimp [t]; linarith only [ef0.upperV,same]
  have sharpV : E.loV+C.side≤t-(2/5)*d := by
    apply le_of_not_gt; intro no
    have capG : E.loU+C.side≤d+(2/5)*t := by
      apply le_of_not_gt; intro high; apply h.rightG
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [d,t] at high no ⊢ <;>
        linarith only [high,no,same,h.outer.1,h.outer.2.2.1,ep,en.1,en.2.1]
    rcases axes with cu | eu
    · rw [lowSupport] at cu
      have w1 := mul_le_mul_of_nonneg_left capG kn
      have w2 := mul_le_mul_of_nonneg_left weakV jp.le
      have margin := first_exit c s d t cf ef (by dsimp [t]; linarith only [negative])
      change k*(d+(2/5)*t)+j*t<k+j at margin
      have excess := mul_nonneg (sub_nonneg.mpr side.le) (add_nonneg kn jp.le)
      nlinarith only [cu,w1,w2,margin,excess,ap]
    · rw [highSupport] at eu
      have w := mul_le_mul_of_nonneg_left caps.2 jp.le
      have margin := first_target c s d t cf ef (by dsimp [t]; linarith only [negative])
      change d+(2/5)*t+(7/20)*j*(c+s)<1+j at margin
      have excess := mul_pos (sub_pos.mpr side) (show 0<1+j by linarith only [jp])
      nlinarith only [eu,w,capG,ownK,margin,excess]
  have highU : E.loU+C.side≤d+t := by dsimp [d,t]; linarith only [ef0.upperU,same]
  have necessary : 1+j<d+t+j*(C.loV+C.side) := by
    rcases axes with cu | eu
    · rw [lowSupport] at cu
      have w1 := mul_le_mul_of_nonneg_left highU kn
      have w2 := mul_le_mul_of_nonneg_left sharpV jp.le
      have margin := final_source c s d t cf ef (by dsimp [t]; linarith only [negative])
      change k*(d+t)+j*(t-(2/5)*d)<k+j at margin
      have excess := mul_nonneg (sub_nonneg.mpr side.le) (add_nonneg kn jp.le)
      exact False.elim (by nlinarith only [cu,w1,w2,margin,excess,ap])
    · rw [highSupport] at eu
      have excess := mul_pos (sub_pos.mpr side) (show 0<1+j by linarith only [jp])
      nlinarith only [eu,ownK,highU,excess]
  have small := (shallow c s d t (C.loV+C.side) cf ef caps.2 necessary).2
  have close : 99/100<C.c := by
    have product := mul_pos (show 0<7/50-C.s by exact small)
      (show 0<7/50+C.s by linarith only [cn.1])
    nlinarith only [product,C.unit_normal,cp]
  refine ⟨negative,⟨en,h.successorMarker,h.near,h.halfpoint,ef0.lowerU,
    ef0.upperU,ef0.lowerV,?_⟩,close,small,necessary⟩
  dsimp [d,t] at sharpV
  linarith only [sharpV,same]

private theorem height_margin {c s d t H : ℝ} (cn : Normal c s) (en : Normal d t)
    (close : 99/100<c) (small : s<7/50) (tp : 0<t)
    (angle : 157/843<half d t)
    (necessary : 1+(c*t+s*d)<d+t+(c*t+s*d)*H) :
    93/500+(33/50)*s<H := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [close]
  have zc : half c s<2/25 := by
    apply (div_lt_iff₀ (by linarith only [cp] : 0<1+c)).mpr
    linarith only [close,small]
  have onec := BottomAngle.half_identity cn
  have oned := BottomAngle.half_identity en
  have weighted := mul_le_mul_of_nonneg_left zc.le cn.1
  have sum : 1+(23/25)*s≤c+s := by linarith only [onec,weighted]
  have jbound : t*(c+s)≤c*t+s*d := by
    have product := mul_nonneg cn.1 (sub_nonneg.mpr en.2.1)
    nlinarith only [product]
  apply lt_of_not_ge
  intro low
  have factor : 0<1-(93/500+(33/50)*s) := by linarith only [small]
  have qbound := mul_le_mul_of_nonneg_right sum factor.le
  have bracket : 0≤s*(1111/12500-(759/1250)*s) :=
    mul_nonneg cn.1 (by linarith only [small])
  have margin : 1-half d t<(c+s)*(1-(93/500+(33/50)*s)) := by
    nlinarith only [qbound,bracket,angle]
  have scaled := mul_lt_mul_of_pos_left margin tp
  have floor := mul_le_mul_of_nonneg_right jbound factor.le
  have jp : 0≤c*t+s*d := add_nonneg (mul_nonneg cp.le tp.le)
    (mul_nonneg cn.1 (by linarith only [eb.1]))
  have cap := mul_le_mul_of_nonneg_left low jp
  nlinarith only [scaled,floor,cap,necessary,oned]

/-- The two bounds used by the independent northwest comparison are
conclusions of the actual southeast comparison, including at C.s=0. -/
theorem bounds (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c C.s) (ep : 0<E.c) (canonical : |E.s|≤E.c)
    (h : Input C E) :
    99/100<C.c ∧ C.s<7/50 ∧
      93/500+(33/50)*C.s<C.loV+C.side ∧ C.loU+C.side≤(7/50)*C.c-C.s/2 := by
  have result := successor_profile C E side same cn ep canonical h
  have negative := result.1
  have e := result.2.1
  have close := result.2.2.1
  have small := result.2.2.2.1
  have necessary := result.2.2.2.2
  have eside : 1<E.side := by simpa only [←same] using side
  have angle := width_half (343/500) e.normal (by norm_num)
    (show 1< -E.s+(343/500)*E.c by linarith only [e.lowerV,e.upperV,eside])
  norm_num at angle
  have height := height_margin cn e.normal close small (by linarith only [negative]) angle necessary
  have point := successor_sharp E eside e
  have cap : C.loU+C.side≤(7/50)*C.c-C.s/2 := by
    apply le_of_not_gt
    intro high
    apply h.apart (7/50) (-1/2)
    refine ⟨?_,point⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.center.1,h.center.2.2.2,h.tip.2.2.1,close,small,cn.1]
  exact ⟨close,small,height,cap⟩

#print axioms successor_profile
#print axioms bounds
end N12Compact.C1092MPPMCenteredPositive
