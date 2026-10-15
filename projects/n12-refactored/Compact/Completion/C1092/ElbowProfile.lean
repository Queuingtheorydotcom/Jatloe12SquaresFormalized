import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.C1092.RigidCharts
import Compact.Geometry.C977CornerCubic

/-! The sharper residual-elbow profile from the actual strict anchors and
five weak exclusions. The shared three-anchor proof supplies its sign and
crosspoint; no ordinary/inward ownership catalogue is assumed. -/
namespace N12Compact.C1092ElbowProfile
open S12 S12Pilot C977CornerCubic C1092RigidCharts
set_option Elab.async false

private def mirror (C : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (translate (pullX C) 4 0))

private theorem inside_mirror (C : OpenSquare) (x y : ℝ) :
    (mirror C).Inside x y ↔ C.Inside (-x) y := by
  rw [mirror,turnFrame_inside,turnFrame_inside,inside_translate,inside_pullX]
  rw [show 4-(x+4)=-x by ring,show y+0=y by ring]

structure Profile (C : OpenSquare) : Prop where
  normal : Normal C.c C.s
  sinePositive : 0<C.s
  lowerU : -C.c-(2/5)*C.s≤C.loU
  upperU : C.loU+C.side≤-(13/50)*C.s
  lowerV : (2/5)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤(7/20)*(C.c+C.s)
  crosspoint : C.Inside 0 (-1/2)
  halfSmall : C.s/(1+C.c)<7/50
  cosine : 24/25<C.c
  sine : C.s<7/25
  sum : C.c+C.s<31/25

theorem canonical_profile (C : OpenSquare) (side : 1<C.side)
    (cp : 0<C.c) (range : |C.s|≤C.c)
    (M : C.Inside (-7/20) (-7/20)) (P : C.Inside (-1) (-13/50))
    (Q : C.Inside (-13/50) 0) (N : ¬C.Inside (-7/20) (7/20))
    (G : ¬C.Inside (-1) (-2/5)) (R : ¬C.Inside (-543/500) 0)
    (T : ¬C.Inside 0 (-13/50)) (B : ¬C.Inside (-2/5) (-1)) : Profile C := by
  classical
  let E := mirror C
  have ec : 0<E.c := by dsimp [E,mirror,turnFrame,translate,pullX]; linarith only [cp]
  have eM : E.Inside (7/20) (-7/20) := by
    apply (inside_mirror C _ _).mpr
    norm_num
    exact M
  have eP : E.Inside 1 (-13/50) := by
    apply (inside_mirror C _ _).mpr
    norm_num
    exact P
  have eQ : E.Inside (13/50) 0 := by
    apply (inside_mirror C _ _).mpr
    norm_num
    exact Q
  have eN : ¬E.Inside (7/20) (7/20) := by
    intro h
    have h' := (inside_mirror C _ _).mp h
    norm_num at h'
    exact N h'
  have eG : ¬E.Inside 1 (-2/5) := by
    intro h
    have h' := (inside_mirror C _ _).mp h
    norm_num at h'
    exact G h'
  have eR : ¬E.Inside (543/500) 0 := by
    intro h
    have h' := (inside_mirror C _ _).mp h
    norm_num at h'
    exact R h'
  have sp : 0<C.s := by
    apply lt_of_not_ge
    intro sign
    exact Completion.OtherCases.ElbowPoint.positive_impossible E side ec
      (by dsimp [E,mirror,turnFrame,translate,pullX]; linarith only [sign])
      (by dsimp [E,mirror,turnFrame,translate,pullX]; linarith only [(abs_le.mp range).1])
      eM eP eN eG
  have cn : Normal C.c C.s := ⟨sp.le,(abs_le.mp range).2,C.unit_normal⟩
  have cb := normal_bounds cn
  have faces := Completion.OtherCases.ElbowPoint.negative_faces E side ec
    (by dsimp [E,mirror,turnFrame,translate,pullX]; linarith only [sp])
    (by dsimp [E,mirror,turnFrame,translate,pullX]; linarith only [(abs_le.mp range).2])
    eM eQ eP eN eG eR
  have lowU : -C.c-(2/5)*C.s≤C.loU := by
    dsimp [E,mirror,turnFrame,translate,pullX] at faces
    linarith only [faces.1]
  have capV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    dsimp [E,mirror,turnFrame,translate,pullX] at faces
    linarith only [faces.2]
  have point := (Completion.OtherCases.ElbowPoint.points E side eM eQ eP eN eG eR).1
  have cross : C.Inside 0 (-1/2) := by
    have h := (inside_mirror C _ _).mp point
    norm_num at h
    exact h
  have chordT := (short_projections C (61/100) (7/20) (by norm_num)).2.1
  have vLow : C.loV< -(13/50)*C.c := by linarith only [capV,side,chordT]
  have capU : C.loU+C.side≤-(13/50)*C.s := by
    apply le_of_not_gt
    intro failure
    apply T
    dsimp [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,Q.1,Q.2.2.2,vLow,cp,sp,cn.2.1]
  have chordB := (short_projections C (2/5) (37/50) (by norm_num)).2.1
  have uLow : C.loU< -(2/5)*C.c-C.s := by linarith only [capU,side,chordB]
  have lowV : (2/5)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro failure
    apply B
    dsimp [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,uLow,M.2.1,P.2.2.2,cp,sp]
  have width : 1<C.c+(7/50)*C.s := by linarith only [lowU,capU,side]
  let z := C.s/(1+C.c)
  have denominator : 0<1+C.c := by linarith only [cp]
  have zp : 0<z := div_pos sp denominator
  have angle : z*(1+C.c)=C.s := by dsimp [z]; field_simp [denominator.ne']
  have unitAngle : C.s*z=1-C.c := by
    dsimp [z]
    field_simp [denominator.ne']
    nlinarith only [C.unit_normal]
  have zh : z<7/50 := by
    apply lt_of_not_ge
    intro failure
    have product := mul_nonneg sp.le (show 0≤z-7/50 by linarith only [failure])
    nlinarith only [product,unitAngle,width]
  have sine : C.s<7/25 := by
    have product := mul_nonneg zp.le (sub_nonneg.mpr cb.2.1)
    nlinarith only [angle,product,zh]
  have cosine : 24/25<C.c := by
    have product := mul_pos sp (sub_pos.mpr zh)
    nlinarith only [product,unitAngle,sine]
  have cform : (1+z^2)*C.c=1-z^2 := by
    have product := congrArg (fun a : ℝ => a*z) angle
    dsimp at product
    nlinarith only [product,unitAngle]
  have sform : (1+z^2)*C.s=2*z := by
    have product := congrArg (fun a : ℝ => a*z) unitAngle
    dsimp at product
    nlinarith only [product,angle]
  have polynomial : 0<6/25-2*z+(56/25)*z^2 := by
    have product := mul_nonneg (sub_nonneg.mpr zh.le)
      (show 0≤2-(56/25)*(7/50+z) by linarith only [zh])
    nlinarith only [product]
  have sum : C.c+C.s<31/25 := by
    have identity : (1+z^2)*(31/25-(C.c+C.s))=6/25-2*z+(56/25)*z^2 := by
      linear_combination -cform-sform
    apply lt_of_not_ge
    intro failure
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+z^2 by positivity) (show 31/25-(C.c+C.s)≤0 by linarith only [failure])
    linarith only [identity,polynomial,product]
  exact ⟨cn,sp,lowU,capU,lowV,capV,cross,zh,cosine,sine,sum⟩

theorem exists_profile (C : OpenSquare) (side : 1<C.side)
    (M : C.Inside (-7/20) (-7/20)) (P : C.Inside (-1) (-13/50))
    (Q : C.Inside (-13/50) 0) (N : ¬C.Inside (-7/20) (7/20))
    (G : ¬C.Inside (-1) (-2/5)) (R : ¬C.Inside (-543/500) 0)
    (T : ¬C.Inside 0 (-13/50)) (B : ¬C.Inside (-2/5) (-1)) :
    ∃ E : OpenSquare, E.side=C.side ∧ (∀ x y, E.Inside x y ↔ C.Inside x y) ∧ Profile E := by
  obtain ⟨E,ec,range,shape,inside,_⟩ := ClosedFrames.canonical_frame C
  refine ⟨E,shape,inside,canonical_profile E (by simpa only [shape] using side) ec range
    ((inside _ _).mpr M) ((inside _ _).mpr P) ((inside _ _).mpr Q)
    (fun h => N ((inside _ _).mp h)) (fun h => G ((inside _ _).mp h))
    (fun h => R ((inside _ _).mp h)) (fun h => T ((inside _ _).mp h))
    (fun h => B ((inside _ _).mp h))⟩

#print axioms exists_profile
end N12Compact.C1092ElbowProfile
