import Compact.Completion.C1092.MPPMCenteredPositiveHeightAxes

/-! CENTERED-POSITIVE-INWARD-ENDING sections 6--8. The full actual
predecessor face table is joined to every surviving SAT source. The
before-angle central support uses a shorter uniform bound in place of
the manuscript's derivative estimate; its strict reserve is .0136. -/
namespace N12Compact.C1092MPPMCenteredPositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds C1092WholeSupports
open C1092MPPMInwardFinal C1092TwoFifths.Support
set_option Elab.async false
noncomputable section

private theorem positive_height (C W : OpenSquare) (h : HeightInput C W)
    (wn : Normal W.c W.s) : C.loV+C.side<17/125+C.s := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [h.close]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonnegative_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let delta := C.c*W.s-C.s*W.c
  have kp : 0<k := by
    have first := mul_pos cp wp
    have last := mul_nonneg h.normal.1 wn.1
    dsimp [k]
    nlinarith only [first,last]
  have ku : k≤1 := dot_le_one h.normal wn
  have Ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  apply lt_of_not_ge
  intro high
  rcases positive_height_axes C W h wn with current|own
  · rcases le_total delta 0 with before|after
    · have order : W.s≤C.s := sine_order h.normal wn before
      have formula := lower_np W (-C.s) C.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) before kp.le
      have Jlow : -(13/50)≤W.loU+W.side := by
        linarith only [h.previous.near.2.1,wb.2.1,wn.1]
      have Qhigh : W.loV<43/500+C.s := by
        linarith only [table.1,h.same,h.side,wb.2.1,order]
      have first := mul_nonpos_of_nonpos_of_nonneg before
        (show 0≤W.loU+W.side+13/50 by linarith only [Jlow])
      have minus : -delta≤C.s := by
        have product := mul_nonneg h.normal.1 (show 0≤1-W.c by linarith only [wb.2.1])
        have cross := mul_nonneg cp.le wn.1
        dsimp [delta]
        nlinarith only [product,cross]
      have last := mul_lt_mul_of_pos_left Qhigh kp
      have reserve := mul_nonneg (show 0≤1-k by linarith only [ku])
        (show 0≤43/500+C.s by linarith only [h.normal.1])
      nlinarith only [current,formula,first,minus,last,reserve,high,h.small]
    · have formula := lower_nn W (-C.s) C.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) after kp.le
      rcases table.2 with topV|topU
      · have Pneg : W.loU≤0 := by linarith only [h.previous.marker.1,wn.2.1]
        have Qhigh : W.loV<43/500 := by linarith only [topV,h.same,h.side,wb.2.1]
        have first := mul_nonpos_of_nonneg_of_nonpos after Pneg
        have last := mul_lt_mul_of_pos_left Qhigh kp
        nlinarith only [current,formula,first,last,ku,high,h.normal.1]
      · have first := mul_nonneg after
          (show 0≤(543/500)*W.s-C.side-W.loU by linarith only [topU.1,h.same])
        have strict := mul_pos (sub_pos.mpr h.side)
          (show 0<delta+k by linarith only [after,kp])
        rcases topU.2 with upper|lower
        · have last := mul_nonneg kp.le
            (show 0≤W.c+W.s-C.side-W.loV by linarith only [upper,h.same])
          have bound : C.loV+C.side<delta*((543/500)*W.s-1)+k*(W.c+W.s-1) := by
            nlinarith only [current,formula,first,last,strict]
          have identity : delta*((543/500)*W.s-1)+k*(W.c+W.s-1)=
              C.c*((W.c+W.s-1)^2/2+(43/500)*W.s^2)+
                C.s*(W.s^2+W.c-W.s-(43/500)*W.c*W.s) := by
            dsimp [delta,k]
            linear_combination (C.c/2)*W.unit_normal
          have one := mul_lt_mul_of_pos_left (cap_f0 wn).1 cp
          have two := mul_le_mul_of_nonneg_left (positive_coefficients_upper wn).1 h.normal.1
          rw [identity] at bound
          nlinarith only [bound,one,two,cb.2.1,high]
        · have last := mul_nonneg kp.le
            (show 0≤(543/500)*W.c+W.s-C.side-W.loV by linarith only [table.1,h.same])
          have bound : C.loV+C.side<delta*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1) := by
            nlinarith only [current,formula,first,last,strict]
          have identity : delta*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1)=
              C.c*(43/500+(W.c+W.s-1)^2/2)+C.s*(W.s^2+W.c-W.s) := by
            dsimp [delta,k]
            linear_combination ((293/500)*C.c)*W.unit_normal
          have one := mul_lt_mul_of_pos_left (cap_g0 wn lower.2.2).1 cp
          have two := mul_le_mul_of_nonneg_left (positive_coefficients_upper wn).2 h.normal.1
          rw [identity] at bound
          nlinarith only [bound,one,two,cb.2.1,high]
  · rcases le_total delta 0 with before|after
    · have order : W.s≤C.s := sine_order h.normal wn before
      have kc : C.c≤k := by
        have first := mul_nonneg (show 0≤1-C.c by linarith only [cb.2.1])
          (show 0≤1-W.c by linarith only [wb.2.1])
        have last := mul_nonneg wp.le (show 0≤1-W.c by linarith only [wb.2.1])
        have cross := mul_nonneg wn.1 (sub_nonneg.mpr order)
        dsimp [k]
        nlinarith only [first,last,cross,wn.2.2]
      have formula : upper C (-W.s) W.c= -delta*(C.loU+C.side)+k*(C.loV+C.side) := by
        rw [(formulas C (-W.s) W.c).2]
        have u : -W.s*C.c+W.c*C.s= -delta := by dsimp [delta]; ring
        have v : -(-W.s)*C.s+W.c*C.c=k := by dsimp [k]; ring
        rw [u,v,max_eq_left (neg_nonneg.mpr before),max_eq_left kp.le]
        ring
      have first := mul_nonneg (neg_nonneg.mpr before) Ap.le
      have last := mul_nonneg kp.le (show 0≤C.loV+C.side-(17/125+C.s) by linarith only [high])
      have reserve := mul_nonneg (show 0≤k-99/100 by linarith only [kc,h.close])
        (show 0≤17/125+C.s by linarith only [h.normal.1])
      have Qhigh : W.loV<43/500+C.s := by
        linarith only [table.1,h.same,h.side,wb.2.1,order]
      nlinarith only [own,formula,first,last,reserve,Qhigh,h.small]
    · have formula := upper_np C (-W.s) W.c (-delta) k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) (neg_nonpos.mpr after) kp.le
      have first := mul_nonneg after
        (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.cap])
      have last := mul_nonneg kp.le
        (show 0≤C.loV+C.side-(17/125+C.s) by linarith only [high])
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+delta by linarith only [after])
      have margin := positive_own_margin h.normal wn h.close h.small
      change 0<1-(543/500)*W.c-W.s+delta*(1-(7/50)*C.c+C.s/2)+k*(17/125+C.s) at margin
      nlinarith only [own,formula,first,last,strict,margin,table.1,h.same]

private theorem nonpositive_height (C W : OpenSquare) (h : HeightInput C W)
    (wn : Normal W.c (-W.s)) : C.loV+C.side<17/125+C.s := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [h.close]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonpositive_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let j := C.s*W.c-C.c*W.s
  have kp : 0<k := by
    have first := mul_pos wp (show 0<C.c-C.s by linarith only [h.close,h.small])
    have last := mul_nonneg h.normal.1 (show 0≤W.c+W.s by linarith only [wn.2.1])
    dsimp [k]
    nlinarith only [first,last]
  have jn : 0≤j := by
    have first := mul_nonneg h.normal.1 wp.le
    have last := mul_nonneg cp.le wn.1
    dsimp [j]
    nlinarith only [first,last]
  have Ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  apply lt_of_not_ge
  intro high
  rcases nonpositive_height_axes C W h wn with current|left|right
  · have formula := lower_np W (-C.s) C.c (-j) k
      (by dsimp [j]; ring) (by dsimp [k]; ring) (neg_nonpos.mpr jn) kp.le
    have first := mul_nonneg jn (show 0≤W.loU+W.c-W.s by linarith only [table.1])
    have last := mul_nonneg kp.le
      (show 0≤(543/500)*W.c-C.side-W.loV by linarith only [table.2,h.same])
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<j+k by linarith only [jn,kp])
    have bound : C.loV+C.side<j*(W.c-W.s-1)+k*((543/500)*W.c-1) := by
      rw [←h.same] at formula
      nlinarith only [current,formula,first,last,strict]
    have identity : j*(W.c-W.s-1)+k*((543/500)*W.c-1)=
        C.c*((43/500)*W.c^2+f W.c (-W.s))+
          C.s*(g W.c (-W.s)+(43/500)*W.c*W.s) := by
      dsimp [j,k,f,g]
      linear_combination (C.c/2)*W.unit_normal
    have one := mul_lt_mul_of_pos_left (cap_negative_fg wn).1 cp
    have two := mul_le_mul_of_nonneg_left (negative_coefficient_upper wn) h.normal.1
    rw [identity] at bound
    dsimp only [g] at bound
    nlinarith only [bound,one,two,cb.2.1,high]
  · have formula := upper_np C (-W.c) (-W.s) (-k) j
      (by dsimp [k]; ring) (by dsimp [j]; ring) (neg_nonpos.mpr kp.le) jn
    have cap : C.loU+C.side≤7/50 := by linarith only [h.cap,cb.2.1,h.normal.1]
    have first := mul_pos kp (show 0<C.side-(C.loU+C.side)-43/50 by linarith only [cap,h.side])
    have last := mul_nonneg jn (show 0≤C.loV+C.side-(17/125+C.s) by linarith only [high])
    have marker : -(W.loU+W.side)<(7/20)*(W.c-W.s) := by
      linarith only [h.previous.marker.2.1]
    have margin := negative_left_margin h.normal wn h.close
    change 0<(43/50)*k+j*(17/125+C.s)-(7/20)*(W.c-W.s) at margin
    nlinarith only [left,formula,first,last,marker,margin]
  · have formula : upper C (-W.s) W.c=j*(C.loU+C.side)+k*(C.loV+C.side) := by
      rw [(formulas C (-W.s) W.c).2]
      have u : -W.s*C.c+W.c*C.s=j := by dsimp [j]; ring
      have v : -(-W.s)*C.s+W.c*C.c=k := by dsimp [k]; ring
      rw [u,v,max_eq_left jn,max_eq_left kp.le]
      ring
    have first := mul_nonneg jn Ap.le
    have last := mul_nonneg kp.le (show 0≤C.loV+C.side-(17/125+C.s) by linarith only [high])
    have margin := negative_right_margin h.normal wn h.close h.small
    change 43/500<k*(17/125+C.s) at margin
    have Qhigh : W.loV<43/500 := by linarith only [table.2,h.same,h.side,wb.2.1]
    nlinarith only [right,formula,first,last,margin,Qhigh]

theorem height (C W : OpenSquare) (side : 1<C.side) (same : C.side=W.side)
    (cn : Normal C.c C.s) (close : 99/100<C.c) (small : C.s<7/50)
    (center : C.Inside 0 0) (marker : C.Inside (-7/20) (-7/20))
    (cap : C.loU+C.side≤(7/50)*C.c-C.s/2)
    (previous : PredecessorPoints W) (canonical : |W.s|≤W.c)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) :
    C.loV+C.side<17/125+C.s := by
  have h : HeightInput C W := ⟨side,same,cn,close,small,center,marker,cap,previous,apart⟩
  by_cases sign : 0≤W.s
  · exact positive_height C W h
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,W.unit_normal⟩
  · exact nonpositive_height C W h
      ⟨by linarith only [sign],by linarith only [(abs_le.mp canonical).1],by nlinarith only [W.unit_normal]⟩

end
#print axioms height
end N12Compact.C1092MPPMCenteredPositive
