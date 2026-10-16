import Compact.Completion.C1092.MPPMInwardFinalBarProfile
import Compact.Completion.C1092.InwardCenterDiagonal

/-! The actual face producers shared by the centered negative cap and
angle chapters. The predecessor table retains both signs, every literal
corner/marker omission, and all alternative faces. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
open C1092RigidCharts CommonCases.CanonicalProjection
set_option Elab.async false

theorem centered_marker_caps (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (center : C.Inside 0 0)
    (marker : C.Inside (-7/20) (-7/20))
    (southeast : ¬C.Inside (7/20) (-7/20))
    (northwest : ¬C.Inside (-7/20) (7/20)) :
    C.loU+C.side≤(7/20)*(C.c-C.s) ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have first : C.loU+C.side≤(7/20)*(C.c-C.s) := by
    apply le_of_not_gt
    intro high
    apply southeast
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [center.1,center.2.2.2,marker.2.2.1,high,cp,cn.1,cn.2.1]
  have chord := (short_projections C (7/10) (-7/10) (by norm_num)).2.1
  have last : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro high
    apply northwest
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [center.2.1,center.2.2.1,first,chord,side,high,cp,cn.1,cn.2.1]
  exact ⟨first,last⟩

theorem centered_lower_face (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (marker : C.Inside (-7/20) (-7/20))
    (inner : C.Inside 0 (-13/50))
    (height : C.loV+C.side≤(7/20)*(C.c+C.s))
    (nonordinary : ¬(C.Inside (-1) (-13/50) ∧ C.Inside (-1) (-2/5))) :
    -C.c-(13/50)*C.s≤C.loU := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  by_cases outer : C.Inside (-1) (-2/5)
  · have missing : ¬C.Inside (-1) (-13/50) := fun own => nonordinary ⟨own,outer⟩
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,marker.2.1,outer.2.2.1,inner.2.2.2,cp,cn.1,cn.2.1]
  · have short := (short_projections C (3/4) (-13/20) (by norm_num)).2.1
    have stronger : -C.c-(2/5)*C.s≤C.loU := by
      apply le_of_not_gt
      intro low
      apply outer
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,marker.2.1,marker.2.2.2,height,side,short,cp,cn.1,cn.2.1]
    linarith only [stronger,cn.1]

theorem successor_sharp (E : OpenSquare) (side : 1<E.side) (e : NegativeSuccessor E) :
    E.Inside (7/50) (-1/2) := by
  have a := (short_projections E (43/50) (-1/2) (by norm_num)).2.1
  have b := (short_projections E (7/50) (-6/25) (by norm_num)).2.1
  have c := (short_projections E (43/50) (1/10) (by norm_num)).2.2.2
  have d := (short_projections E (7/50) (293/500) (by norm_num)).2.2.2
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [a,b,c,d,e.lowerU,e.upperU,e.lowerV,e.upperV,side]

theorem centered_first_cap (C E : OpenSquare) (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c (-C.s)) (center : C.Inside 0 0)
    (marker : C.Inside (-7/20) (-7/20))
    (southeast : ¬C.Inside (7/20) (-7/20))
    (northwest : ¬C.Inside (-7/20) (7/20))
    (e : NegativeSuccessor E) (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤(7/50)*C.c-C.s/2 := by
  have diagonal' := C1092InwardCenterDiagonal.long_point (opposite C) side
    (by simpa only [inside_opposite,neg_zero] using center)
    (by norm_num [inside_opposite]; simpa only [neg_div] using marker)
    (by norm_num [inside_opposite]; simpa only [neg_div] using southeast)
    (by norm_num [inside_opposite]; simpa only [neg_div] using northwest)
  have diagonal : C.Inside (-61/100) (-61/100) := by
    simpa only [inside_opposite,neg_div] using diagonal'
  have sharp := successor_sharp E (by simpa only [←same] using side) e
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  apply le_of_not_gt
  intro high
  apply apart _ _ ⟨?_,sharp⟩
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [center.1,center.2.2.2,diagonal.2.2.1,high,cp,cn.1,cn.2.1]

structure PredecessorPoints (W : OpenSquare) : Prop where
  marker : W.Inside (-7/20) (7/20)
  near : W.Inside (-13/50) 1
  outer : W.Inside (-2/5) 1
  topMarker : ¬W.Inside 0 (543/500)
  corner : ¬W.Inside (-1) 1
  cornerMarker : ¬W.Inside (-1) (543/500)

theorem nonpositive_predecessor_faces (W : OpenSquare) (side : 1<W.side)
    (wn : Normal W.c (-W.s)) (h : PredecessorPoints W) :
    -W.c+W.s≤W.loU ∧ W.loV+W.side≤(543/500)*W.c := by
  have wb := normal_bounds wn
  have wp : 0<W.c := by linarith only [wb.1]
  have floor : -W.c+W.s≤W.loU := by
    apply le_of_not_gt
    intro low
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.near.2.1,h.marker.2.2.1,h.near.2.2.2,wp,wn.1,wn.2.1]
  have cap : W.loV+W.side≤(543/500)*W.c := by
    apply le_of_not_gt
    intro high
    apply h.topMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.near.1,h.marker.2.2.1,floor,side,wb.2.1,high,wp,wn.1,wn.2.1]
  exact ⟨floor,cap⟩

theorem nonnegative_predecessor_faces (W : OpenSquare) (side : 1<W.side)
    (wn : Normal W.c W.s) (h : PredecessorPoints W) :
    W.loV+W.side≤(543/500)*W.c+W.s ∧
      (W.loV+W.side≤(543/500)*W.c ∨
        (W.loU+W.side≤(543/500)*W.s ∧
          (W.loV+W.side≤W.c+W.s ∨
            (-W.c+W.s≤W.loU ∧ half W.c W.s<43/500 ∧ W.c+W.s<29/25)))) := by
  have wb := normal_bounds wn
  have wp : 0<W.c := by linarith only [wb.1]
  have zExit : W.loV+W.side≤(543/500)*W.c ∨ W.loU+W.side≤(543/500)*W.s := by
    by_cases cap : W.loV+W.side≤(543/500)*W.c
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro high
      apply h.topMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.near.1,h.marker.2.2.1,cap,high,wp,wn.1,wn.2.1]
  rcases zExit with topV|topU
  · exact ⟨by linarith only [topV,wn.1],Or.inl topV⟩
  · have always : W.loV+W.side≤(543/500)*W.c+W.s := by
      apply le_of_not_gt
      intro high
      apply h.cornerMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [topU,side,wb.2.1,h.near.2.1,h.marker.2.2.1,high,wp,wn.1,wn.2.1]
    refine ⟨always,Or.inr ⟨topU,?_⟩⟩
    by_cases cap : W.loV+W.side≤W.c+W.s
    · exact Or.inl cap
    · right
      have floor : -W.c+W.s≤W.loU := by
        apply le_of_not_gt
        intro low
        apply h.corner
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [low,h.near.2.1,h.marker.2.2.1,cap,wp,wn.1,wn.2.1]
      have width : 1<W.c+(43/500)*W.s := by linarith only [floor,topU,side]
      have data := quarter_data W.c W.s wp.le wn.1 wn.2.2
      let z := half W.c W.s
      have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
      have identity : (1+z^2)*(W.c+(43/500)*W.s-1)=2*z*(43/500-z) := by
        nlinarith only [data.2.2.2.1,data.2.2.2.2]
      have positive := mul_pos den (sub_pos.mpr width)
      have small : z<43/500 := by
        apply lt_of_not_ge
        intro large
        have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*z by linarith only [data.1])
          (show 43/500-z≤0 by linarith only [large])
        nlinarith only [bad,identity,positive]
      have endpoint : Normal (248151/251849) (43000/251849) := by norm_num [Normal]
      have endpointHalf : half (248151/251849) (43000/251849)=(43:ℝ)/500 := by norm_num [half]
      have cross := half_cross wn endpoint (by simpa only [endpointHalf] using small.le)
      have sum := before W.c W.s (248151/251849) (43000/251849) 1 1 wn.2.2 endpoint.2.2
        (by simpa only [mul_comm] using cross) (by norm_num) (by norm_num)
      exact ⟨floor,small,by linarith only [sum]⟩

#print axioms centered_first_cap
#print axioms nonpositive_predecessor_faces
#print axioms nonnegative_predecessor_faces
end N12Compact.C1092MPPMInwardFinal
