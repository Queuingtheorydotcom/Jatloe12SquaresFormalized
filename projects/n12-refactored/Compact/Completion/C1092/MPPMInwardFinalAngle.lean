import Compact.Completion.C1092.MPPMInwardFinalAngleRows
import Compact.Completion.C1092.MPPMInwardFinalHeight
import Compact.Completion.C1092.MPPMInwardFinalCentered
import Compact.Completion.CommonCases.OriginalOwners

/-! The full predecessor normal join of CENTERED-NEGATIVE-INWARD-ANGLE.
This proof does not use the stronger H<.136 conclusion. Every actual
predecessor face row, both signs, and both relative orders remain. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

private theorem positive_angle (C W : OpenSquare) (h : CenteredCapInput C W)
    (wn : Normal W.c W.s) : half C.c (-C.s)<21/100 := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonnegative_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let j := C.c*W.s-C.s*W.c
  have kn : 0≤k := by
    have first := mul_nonneg (show 0≤C.c+C.s by linarith only [h.normal.2.1]) wp.le
    have last := mul_nonneg h.normal.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]; nlinarith only [first,last]
  have jn : 0≤j := by
    have first := mul_nonneg cp.le wn.1
    have last := mul_nonneg h.normal.1 wp.le
    dsimp [j]; nlinarith only [first,last]
  have Hp : 0<C.loV+C.side := by linarith only [h.center.2.2.2]
  apply lt_of_not_ge
  intro low
  have endpoint := angle_endpoint h.normal low
  rcases positive_axes C W h wn with own|last
  · have formula := lower_nn W (-C.s) C.c j k
      (by dsimp [j]; ring) (by dsimp [k]; ring) jn kn
    rcases table.2 with topV|topU
    · have first := mul_nonneg jn
        (show 0≤(7/20)*(W.s-W.c)-W.loU by linarith only [h.previous.marker.1])
      have second := mul_nonneg kn
        (show 0≤(543/500)*W.c-1-W.loV by linarith only [topV,h.side,h.same])
      have bound : C.loV+C.side≤j*((7/20)*(W.s-W.c))+k*((543/500)*W.c-1) := by
        nlinarith only [own,formula,first,second]
      have identity : j*((7/20)*(W.s-W.c))+k*((543/500)*W.c-1)=
          C.c*angleFz W.c W.s+C.s*angleGz W.c W.s := by
        dsimp [j,k,angleFz,angleGz]; ring
      have margin := angle_z_row h.normal wn endpoint.2.2.1
      rw [identity] at bound
      nlinarith only [bound,margin,Hp]
    · have first := mul_nonneg jn
        (show 0≤(543/500)*W.s-1-W.loU by linarith only [topU.1,h.same,h.side])
      rcases topU.2 with upper|lower
      · have second := mul_nonneg kn
          (show 0≤W.c+W.s-1-W.loV by linarith only [upper,h.same,h.side])
        have bound : C.loV+C.side≤j*((543/500)*W.s-1)+k*(W.c+W.s-1) := by
          nlinarith only [own,formula,first,second]
        have identity : j*((543/500)*W.s-1)+k*(W.c+W.s-1)=
            C.c*((W.c+W.s-1)^2/2+(43/500)*W.s^2)+
              C.s*(W.s^2+W.c-W.s-(43/500)*W.c*W.s) := by
          dsimp [j,k]
          linear_combination (C.c/2)*W.unit_normal
        have margin := angle_f0_row h.normal wn endpoint.2.2.1
        rw [identity] at bound
        nlinarith only [bound,margin,Hp]
      · have second := mul_nonneg kn
          (show 0≤(543/500)*W.c+W.s-1-W.loV by linarith only [table.1,h.same,h.side])
        have bound : C.loV+C.side≤j*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1) := by
          nlinarith only [own,formula,first,second]
        have identity : j*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1)=
            C.c*(43/500+(W.c+W.s-1)^2/2)+C.s*(W.s^2+W.c-W.s) := by
          dsimp [j,k]
          linear_combination ((293/500)*C.c)*W.unit_normal
        have margin := angle_g0_row h.normal wn endpoint.2.2.1 lower.2.1 lower.2.2
        rw [identity] at bound
        nlinarith only [bound,margin,Hp]
  · have formula := upper_np C (-W.s) W.c (-j) k
      (by dsimp [j]; ring) (by dsimp [k]; ring) (by linarith only [jn]) kn
    have first := mul_nonneg jn
      (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
    have second := mul_nonneg kn Hp.le
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+j by linarith only [jn])
    have margin := angle_own_positive h.normal wn low
    dsimp [centeredD,j,k] at formula first second strict margin
    nlinarith only [last,formula,first,second,strict,margin,table.1,h.same]

private theorem nonpositive_angle (C W : OpenSquare) (h : CenteredCapInput C W)
    (wn : Normal W.c (-W.s)) : half C.c (-C.s)<21/100 := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonpositive_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let delta := C.s*W.c-C.c*W.s
  have relative := C1092MMMPUpperThirdScalars.relative_bounds h.normal wn
  have kp : 0<k := by dsimp [k]; nlinarith only [relative.1]
  have Ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  have Aback : 0< -C.loU := by linarith only [h.center.1]
  have Hp : 0<C.loV+C.side := by linarith only [h.center.2.2.2]
  have Hback : 0< -C.loV := by linarith only [h.center.2.2.1]
  apply lt_of_not_ge
  intro low
  have endpoint := angle_endpoint h.normal low
  rcases upward_axes C W h.same cp (by linarith only [h.normal.1]) wp
      (by linarith only [wn.1]) h.marker h.previous.marker h.apart with first|own|wu|wv
  · exact reject_first C W h first
  · by_cases order : delta≤0
    · have formula := lower_nn W (-C.s) C.c (-delta) k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) (by linarith only [order]) kp.le
      have first := mul_nonneg (show 0≤-delta by linarith only [order])
        (show 0≤-(7/20)*(W.c-W.s)-W.loU by linarith only [h.previous.marker.1])
      have second := mul_nonneg kp.le
        (show 0≤(543/500)*W.c-1-W.loV by linarith only [table.2,h.side,h.same])
      have bound : C.loV+C.side≤(-delta)*(-(7/20)*(W.c-W.s))+k*((543/500)*W.c-1) := by
        nlinarith only [own,formula,first,second]
      have identity : (-delta)*(-(7/20)*(W.c-W.s))+k*((543/500)*W.c-1)=
          C.c*angleFl W.c (-W.s)+C.s*angleGl W.c (-W.s) := by
        dsimp [delta,k,angleFl,angleGl]; ring
      have margin := angle_left_row h.normal wn endpoint.2.1
      rw [identity] at bound
      nlinarith only [bound,margin,Hp]
    · have dp : 0<delta := lt_of_not_ge order
      have formula := lower_np W (-C.s) C.c (-delta) k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) (by linarith only [dp]) kp.le
      have first := mul_nonneg dp.le (show 0≤W.loU+W.c-W.s by linarith only [table.1])
      have second := mul_nonneg kp.le
        (show 0≤(543/500)*W.c-C.side-W.loV by linarith only [table.2,h.same])
      have strict := mul_pos (sub_pos.mpr h.side) (add_pos dp kp)
      have bound : C.loV+C.side<delta*(W.c-W.s-1)+k*((543/500)*W.c-1) := by
        rw [←h.same] at formula
        nlinarith only [own,formula,first,second,strict]
      have identity : delta*(W.c-W.s-1)+k*((543/500)*W.c-1)=
          C.c*((43/500)*W.c^2+f W.c (-W.s))+
            C.s*(g W.c (-W.s)+(43/500)*W.c*W.s) := by
        dsimp [delta,k,f,g]
        linear_combination (C.c/2)*W.unit_normal
      have wlow : 21/100≤half W.c (-W.s) := by
        apply le_of_not_gt
        intro small
        have backwards := relative_order wn h.normal (by linarith only [small,low])
        dsimp [delta] at dp
        nlinarith only [backwards,dp]
      have margin := angle_right_row h.normal wn endpoint.2.1 wlow
      rw [identity] at bound
      nlinarith only [bound,margin,Hp]
  · have first := mul_nonneg kp.le
      (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k by linarith only [kp])
    have margin := angle_left h.normal wn low
    by_cases order : 0≤delta
    · have formula := upper_np C (-W.c) (-W.s) (-k) delta
        (by dsimp [k]; ring) (by dsimp [delta]; ring) (by linarith only [kp]) order
      have last := mul_nonneg order Hp.le
      dsimp [centeredD,k,delta] at formula first last strict margin
      nlinarith only [wu,formula,first,last,strict,margin,table.1,h.same]
    · have formula := upper_neg_neg C (-W.c) (-W.s) (-k) delta
        (by dsimp [k]; ring) (by dsimp [delta]; ring) (by linarith only [kp]) (by linarith only [order])
      have last := mul_nonneg (show 0≤-delta by linarith only [order]) Hback.le
      dsimp [centeredD,k,delta] at formula first last strict margin
      nlinarith only [wu,formula,first,last,strict,margin,table.1,h.same]
  · by_cases order : 0≤delta
    · have formula := upper_pos_pos C (-W.s) W.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) order kp.le
      have first := mul_nonneg order Ap.le
      have last := mul_pos kp Hp
      have cosines := coordinates_after wn h.normal (by dsimp [delta] at order; nlinarith only [order])
      nlinarith only [wv,formula,first,last,table.2,h.same,h.side,cosines.1,endpoint.2.2.2.2]
    · have formula := upper_np C (-W.s) W.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) (by linarith only [order]) kp.le
      have first := mul_nonneg (show 0≤-delta by linarith only [order])
        (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
      have last := mul_nonneg kp.le Hp.le
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<1-delta by linarith only [order])
      have margin := angle_right_before h.normal wn low (by dsimp [delta] at order; nlinarith only [order])
      dsimp [centeredD,k,delta] at formula first last strict margin
      nlinarith only [wv,formula,first,last,strict,margin,table.2,h.same]

theorem centered_half_angle (C W : OpenSquare) (h : CenteredCapInput C W)
    (canonical : |W.s|≤W.c) : half C.c (-C.s)<21/100 := by
  by_cases sign : 0≤W.s
  · exact positive_angle C W h ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,W.unit_normal⟩
  · have wn : Normal W.c (-W.s) :=
      ⟨by linarith only [sign],by linarith only [(abs_le.mp canonical).1],by nlinarith only [W.unit_normal]⟩
    exact nonpositive_angle C W h wn

theorem centered_outer_halfpoint (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (negative : C.s<0)
    (marker : C.Inside (-7/20) (-7/20))
    (height : C.loV+C.side<17/125) (small : half C.c (-C.s)<21/100)
    (outer : C.Inside (-1) (-13/50) ∨ C.Inside (-1) (-2/5)) :
    C.Inside (-1) (-1/2) := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have endpoint : Normal (9559/10441) (4200/10441) := by norm_num [Normal]
  have endpointHalf : half (9559/10441) (4200/10441)=(21:ℝ)/100 := by norm_num [half]
  have cross := half_cross cn endpoint (by simpa only [endpointHalf] using small.le)
  have projection := CommonCases.CanonicalProjection.before C.c (-C.s)
    (9559/10441) (4200/10441) (1/2) 1 cn.2.2 endpoint.2.2 cross (by norm_num) (by norm_num)
  rcases outer with own|own <;> refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [own.1,own.2.2.2,marker.2.1,height,side,projection,cp,negative,cn.2.1]

theorem centered_outer_consequences (C W : OpenSquare) (h : CenteredCapInput C W)
    (canonical : |W.s|≤W.c) (negative : C.s<0)
    (nonordinary : ¬(C.Inside (-1) (-13/50) ∧ C.Inside (-1) (-2/5))) :
    ¬C.Inside (-1) (-13/50) ∧
      (C.Inside (-1) (-2/5) → C.Inside (-1) (-1/2)) := by
  have height := centered_height_cap C W h canonical
  have angle := centered_half_angle C W h canonical
  constructor
  · intro own
    have far := centered_outer_halfpoint C h.side h.normal negative h.marker height angle (Or.inl own)
    have G := CommonCases.OriginalOwners.vertical_segment C (-1) (-1/2) (-13/50) (-2/5)
      far own (by norm_num) (by norm_num) (by norm_num)
    exact nonordinary ⟨own,G⟩
  · intro own
    exact centered_outer_halfpoint C h.side h.normal negative h.marker height angle (Or.inr own)

theorem centered_outer_origin (C W B K : OpenSquare) (h : CenteredCapInput C W)
    (canonical : |W.s|≤W.c) (negative : C.s<0)
    (nonordinary : ¬(C.Inside (-1) (-13/50) ∧ C.Inside (-1) (-2/5)))
    (outer : C.Inside (-1) (-2/5)) (bottom : BottomCorner B K)
    (apart : ∀ x y,¬(C.Inside x y ∧ K.Inside x y)) : B.Inside 0 (-1) :=
  bottom_origin C B K bottom
    ((centered_outer_consequences C W h canonical negative nonordinary).2 outer) apart

#print axioms centered_half_angle
#print axioms centered_outer_consequences
end N12Compact.C1092MPPMInwardFinal
