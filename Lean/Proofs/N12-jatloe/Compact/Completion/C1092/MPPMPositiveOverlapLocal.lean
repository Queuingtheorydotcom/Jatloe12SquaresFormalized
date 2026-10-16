import Compact.Completion.C1092.MPPMPositiveOverlapScalars
import Compact.Completion.C1092.MPPMNonpositivePredecessor
import Compact.Completion.C1092.MPPMPositiveCrosspointSeeds
import Compact.Completion.C1092.MMMP.NortheastNegativeFaces
import Compact.Completion.C1092.MMMMNegativeNeighbor
import Compact.Completion.C1092.RigidCharts
import S12.Convex

/-! The same actual C/E pair in CENTERED-POSITIVE-OVERLAP. Its point and
axis steps are CENTERED-POSITIVE-INWARD-ENDING sections 1--4. The extra
ordinary predecessor-origin exclusion supplies H≤s, and the scalar file
closes the remaining southeast source. No nonordinary premise, inward
tip, northwest-angle restriction, or upper side bound is used. -/
namespace N12Compact.C1092MPPMPositiveOverlap
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092MPPMOrdinaryNegativeHalfpoint
set_option Elab.async false

structure Inputs (C E : OpenSquare) : Prop where
  core : C1092MPPMPositiveCrosspointSeeds.ForwardInputs C
  inward : C.Inside 0 (-13/50)
  marker : E.Inside (7/20) (-7/20)
  ordinaryP : E.Inside (13/50) (-1)
  ordinaryG : E.Inside (2/5) (-1)
  shortWall : ¬E.Inside 1 (-39/100)
  bottomMarker : ¬E.Inside 0 (-543/500)
  corner : ¬E.Inside 1 (-1)
  rightOrigin : ¬E.Inside 1 0
  rightG : ¬E.Inside 1 (-2/5)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

private theorem center_caps (C E : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : Inputs C E) (origin : C.Inside 0 0) :
    C.loU+C.side≤(7/20)*(C.c-C.s) ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have capV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt; intro high; apply h.core.northMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.core.marker.1,origin.2.1,origin.2.2.1,cp,cn.1,cn.2.1]
  refine ⟨?_,capV⟩
  apply le_of_not_gt; intro high
  have lowV : C.loV< -(7/20)*(C.c+C.s) := by
    linarith only [capV,side,cb.2.2.2.2.2]
  apply h.apart (7/20) (-7/20)
  refine ⟨⟨?_,?_,?_,?_⟩,h.marker⟩ <;>
    linarith only [high,lowV,origin.1,origin.2.2.2,cp,cn.1,cn.2.1]

private theorem lower_crosspoint (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (origin : C.Inside 0 0)
    (left : C.Inside (-1/2) 0)
    (cap : C.loV+C.side≤(7/20)*(C.c+C.s)) : C.Inside 0 (-1/2) := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have norm := C1092MPPMNonpositivePredecessor.norm_lt (17/20) (7/20)
    C.c C.s 1 C.unit_normal (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [origin.2.1,origin.2.2.2,left.1,cap,side,norm,cp,cn.1,cn.2.1]

/-- The transposed nonpositive-neighbor theorem uses only the actual
rectangle endpoints. It does not invoke the stronger chapter conclusion
whose separate extra point is unavailable here. -/
private theorem successor_negative (C E : OpenSquare) (side : 1<C.side)
    (same : C.side=E.side) (cn : Normal C.c C.s) (canonical : |E.s|≤E.c)
    (h : Inputs C E) (origin : C.Inside 0 0)
    (left : C.Inside (-1/2) 0) (bottom : C.Inside 0 (-1/2)) : E.s<0 := by
  apply lt_of_not_ge
  intro sign
  let D := C1092RigidCharts.swap C
  let B := C1092RigidCharts.swap E
  have dActual (x y : ℝ) : D.Inside x y↔C.Inside y x := C1092RigidCharts.inside_swap C x y
  have bActual (x y : ℝ) : B.Inside x y↔E.Inside y x := C1092RigidCharts.inside_swap E x y
  have dn : Normal D.c (-D.s) := by
    change Normal C.c (-(-C.s)); simpa only [neg_neg] using cn
  have bn : Normal B.c (-B.s) := by
    change Normal E.c (-(-E.s))
    simpa only [neg_neg] using
      (show Normal E.c E.s from ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,E.unit_normal⟩)
  have column : C.Inside 0 (-39/100) := by
    have point := inside_segment C 0 0 0 (-1/2) (39/50) origin bottom (by norm_num) (by norm_num)
    norm_num at point
    simpa only [neg_div] using point
  have faces := C1092MMMPNortheastNegativeFaces.faces B bn (by change 1<E.side; rwa [←same])
    ((bActual _ _).mpr h.marker) ((bActual _ _).mpr h.ordinaryP) ((bActual _ _).mpr h.ordinaryG)
    (fun own => h.apart _ _ ⟨column,(bActual _ _).mp own⟩)
    (fun own => h.shortWall ((bActual _ _).mp own))
    (fun own => h.bottomMarker ((bActual _ _).mp own))
    (fun own => h.corner ((bActual _ _).mp own))
    (fun own => h.apart _ _ ⟨bottom,(bActual _ _).mp own⟩)
  exact C1092MMMMNegativeNeighbor.impossible_faces D B side same dn bn
    ((dActual _ _).mpr origin) ((dActual _ _).mpr left) ((dActual _ _).mpr h.core.marker)
    (fun own => h.core.northMarker ((dActual _ _).mp own))
    ((bActual _ _).mpr h.marker) ((bActual _ _).mpr h.ordinaryG)
    (by linarith only [faces.lowerU]) faces.upperU (by linarith only [faces.upperV])
    (fun x y own => h.apart y x ⟨(dActual _ _).mp own.1,(bActual _ _).mp own.2⟩)

structure SuccessorFaces (E : OpenSquare) : Prop where
  lowerU : -(13/50)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -(543/500)*E.c≤E.loV
  upperV : E.loV+E.side≤-E.s

/-- Every face is forced from its literal excluded point. The source's
extra inward tip is absent, so its additional lower-u estimate is omitted. -/
private theorem successor_faces (C E : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (h : Inputs C E) : SuccessorFaces E := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have innerMissing : ¬E.Inside 0 (-13/50) := fun own => h.apart _ _ ⟨h.inward,own⟩
  have low : -(13/50)*E.s≤E.loU := by
    apply le_of_not_gt; intro low
    have highV : E.loV+E.side≤-(13/50)*E.c := by
      apply le_of_not_gt; intro high; apply innerMissing
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,h.marker.2.1,h.ordinaryG.2.2.1,ep,en.1,en.2.1]
    have highU : E.loU+E.side≤E.c-E.s := by
      apply le_of_not_gt; intro high; apply h.corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,highV,side,h.ordinaryG.1,h.marker.2.2.2,eb.2.1,ep,en.1,en.2.1]
    have lowU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt; intro lowU; apply h.bottomMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowU,highV,side,h.ordinaryP.2.1,h.marker.2.2.2,
          eb.2.1,ep,en.1,en.2.1]
    linarith only [lowU,highU,side,eb.2.1,en.1]
  have highV : E.loV+E.side≤-E.s := by
    apply le_of_not_gt; intro high
    have highU : E.loU+E.side≤E.c := by
      apply le_of_not_gt; intro highU; apply h.rightOrigin
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [highU,high,h.marker.1,h.ordinaryG.2.2.1,ep,en.1,en.2.1]
    linarith only [low,highU,side,eb.2.1,en.1]
  have highU : E.loU+E.side≤E.c-E.s := by
    apply le_of_not_gt; intro high; apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,highV,side,h.ordinaryG.1,h.marker.2.2.2,eb.2.1,ep,en.1,en.2.1]
  have lowV : -(543/500)*E.c≤E.loV := by
    apply le_of_not_gt; intro low
    have lowU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt; intro lowU; apply h.bottomMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,lowU,h.ordinaryP.2.1,h.marker.2.2.2,ep,en.1,en.2.1]
    linarith only [lowU,highU,side,eb.2.1,en.1]
  exact ⟨low,highU,lowV,highV⟩

/-- Complete local overlap exclusion from actual point data. The raw
preceding-origin absence is the already proved positive-forward D theorem
in its original application; it is never inferred from an omitted point. -/
theorem center_absent (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c C.s) (ep : 0<E.c) (canonical : |E.s|≤E.c)
    (h : Inputs C E) : ¬C.Inside 0 0 := by
  intro origin
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have cf : Frame C.c C.s := ⟨cp,cn.1,cn.2.1,cn.2.2⟩
  have faces := C1092MPPMPositiveCrosspointSeeds.forward_profile C side cn h.core.core
  have caps := center_caps C E side cn h origin
  have left := C1092MPPMPositiveCrosspointSeeds.crosspoint_of_forward C side cn h.core
  have bottom := lower_crosspoint C side cn origin left caps.2
  have negative := successor_negative C E side same cn canonical h origin left bottom
  have en : Normal E.c (-E.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,by nlinarith only [E.unit_normal]⟩
  have ef : Frame E.c (-E.s) := ⟨ep,en.1,en.2.1,en.2.2⟩
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
  have ap : 0<C.loU+C.side := by linarith only [origin.2.1]
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
        h.core.marker h.marker h.ordinaryP h.apart with cu | cv | eu
    · exact Or.inl cu
    · have strict := (strict_bounds E _ _ C.s (-C.c)
        (by nlinarith only [C.unit_normal]) h.marker).1
      linarith only [cv,strict,caps.2,side,cb.2.2.2.2.2]
    · exact Or.inr eu
  have weakV : E.loV+C.side≤t := by dsimp [t]; linarith only [ef0.upperV,same]
  have sharpV : E.loV+C.side≤t-(2/5)*d := by
    apply le_of_not_gt; intro no
    have capG : E.loU+C.side≤d+(2/5)*t := by
      apply le_of_not_gt; intro high; apply h.rightG
      refine ⟨?_,?_,?_,?_⟩ <;> dsimp [d,t] at high no ⊢ <;>
        linarith only [high,no,same,h.ordinaryG.1,h.ordinaryG.2.2.1,ep,en.1,en.2.1]
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
      have margin' : d+(2/5)*t+(7/20)*j*(c+s)<1+j := by
        dsimp only [j]
        linarith only [margin]
      have excess := mul_pos (sub_pos.mpr side) (show 0<1+j by linarith only [jp])
      nlinarith only [eu,w,capG,ownK,margin',excess]
  have highU : E.loU+C.side≤d+t := by dsimp [d,t]; linarith only [ef0.upperU,same]
  rcases axes with cu | eu
  · rw [lowSupport] at cu
    have w1 := mul_le_mul_of_nonneg_left highU kn
    have w2 := mul_le_mul_of_nonneg_left sharpV jp.le
    have margin := final_source c s d t cf ef (by dsimp [t]; linarith only [negative])
    change k*(d+t)+j*(t-(2/5)*d)<k+j at margin
    have excess := mul_nonneg (sub_nonneg.mpr side.le) (add_nonneg kn jp.le)
    nlinarith only [cu,w1,w2,margin,excess,ap]
  · rw [highSupport] at eu
    have excess := mul_pos (sub_pos.mpr side) (show 0<1+j by linarith only [jp])
    have necessary : 1+j<d+t+j*(C.loV+C.side) := by
      nlinarith only [eu,ownK,highU,excess]
    exact last_impossible c s d t (C.loV+C.side) cf ef caps.2 faces.upperV
      (by dsimp only [j] at necessary; linarith only [necessary])

#print axioms center_absent
end N12Compact.C1092MPPMPositiveOverlap
