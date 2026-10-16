import S12.SquareFrame
import Compact.Completion.C1092.MPPMMissingNegativeProfileScalars

/-! MISSING-NEGATIVE-WALL-ORDER Lemma 1 and MISSING-NEGATIVE-BOUNDARIES
Lemma 1. One proof handles the omitted wall marker and the omitted
preceding origin; the latter does not require the former. The complete
literal excluded segment supplies its own vertex support inequality.
This is source-only work, without compiler or replay acceptance. -/
namespace N12Compact.C1092MPPMMissingNegativeProfile
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure Core (C : OpenSquare) : Prop where
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  ordinaryG : C.Inside (-1) (-2/5)
  halfpoint : C.Inside (-1) (-1/2)
  corner : ¬C.Inside (-1) (-1)
  forward : ¬C.Inside (-13/50) 0
  bar : ∀ x, -(14/25)≤x → x≤-(13/50) → ¬C.Inside x (-1)

structure Faces (C : OpenSquare) : Prop where
  lowerV : C.s-C.c≤C.loV
  upperU : C.loU+C.side≤-C.s-(14/25)*C.c
  upperV : C.loV+C.side≤(13/50)*C.s
  negative : C.s<0
  halfHigh : C1092WallProfileScalars.half C.c (-C.s)<1

structure WeakFaces (C : OpenSquare) extends Faces C : Prop where
  lowerU : -(543/500)*C.c≤C.loU
  widthU : C.side≤(263/500)*C.c-C.s
  halfLow : 237/763<C1092WallProfileScalars.half C.c (-C.s)

structure StrongFaces (C : OpenSquare) extends Faces C : Prop where
  lowerU : -C.c≤C.loU
  widthU : C.side≤(11/25)*C.c-C.s
  halfLow : 7/18<C1092WallProfileScalars.half C.c (-C.s)

private theorem bar_bands (C : OpenSquare) (cn : Normal C.c (-C.s)) (h : Core C)
    (x : ℝ) (low : -(14/25)≤x) (high : x≤-(13/50)) :
    C.loU<C.c*x-C.s ∧ -C.s*x-C.c<C.loV+C.side := by
  have cb := normal_bounds cn
  have first := mul_nonneg (show 0≤C.c by linarith only [cb.1])
    (show 0≤x+14/25 by linarith only [low])
  have last := mul_nonneg cn.1 (show 0≤-(13/50)-x by linarith only [high])
  constructor <;>
    nlinarith only [first,last,h.ordinaryP.1,h.ordinaryP.2.2.2,cb.1,cn.1,cn.2.1]

private theorem point_caps (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (h : Core C) (w : ℝ) (wl : 1≤w) (wh : w≤543/500)
    (missing : ¬C.Inside (-w) 0) :
    C.s-C.c≤C.loV ∧ -w*C.c≤C.loU ∧ C.loV+C.side≤(13/50)*C.s ∧
      C.loU+C.side≤-C.s-(13/50)*C.c ∧ C.s<0 := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have cornerV : C.s-C.c≤C.loV := by
    apply le_of_not_gt; intro low; apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.halfpoint.1,h.marker.2.1,h.ordinaryG.2.2.2,cp,cn.1,cn.2.1]
  have wallUWeight := mul_nonneg (show 0≤w-1 by linarith only [wl]) cp.le
  have wallVWeight := mul_nonneg (show 0≤543/500-w by linarith only [wh]) cn.1
  have wallSign := mul_nonneg (show 0≤w-1 by linarith only [wl]) cn.1
  have wallWidth := mul_nonneg cp.le (show 0≤543/500-w by linarith only [wh])
  have lowerU : -w*C.c≤C.loU := by
    apply le_of_not_gt; intro low
    have upper : C.loV+C.side≤w*C.s := by
      apply le_of_not_gt; intro high; apply missing
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [low,high,h.ordinaryP.2.1,h.ordinaryG.2.2.1,
          wallUWeight,wallVWeight,cp,cn.1,cn.2.1]
    nlinarith only [cornerV,upper,side,cb.2.1,wallSign]
  have upperV : C.loV+C.side≤(13/50)*C.s := by
    apply le_of_not_gt; intro high
    have upper : C.loU+C.side≤-(13/50)*C.c := by
      apply le_of_not_gt; intro highU; apply h.forward
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,highU,h.ordinaryP.1,h.ordinaryP.2.2.1,cp,cn.1,cn.2.1]
    nlinarith only [lowerU,upper,wallWidth,side,cb.2.1]
  have bands := bar_bands C cn h (-(13/50)) (by norm_num) (by norm_num)
  have near : C.loU+C.side≤-C.s-(13/50)*C.c := by
    apply le_of_not_gt; intro high
    apply h.bar (-(13/50)) (by norm_num) (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [bands.1,bands.2,high,upperV,side,cb.2.1]
  have negative : C.s<0 := by nlinarith only [near,lowerU,wallWidth,side,cb.2.1]
  exact ⟨cornerV,lowerU,upperV,near,negative⟩

private theorem vertex (C : OpenSquare) (cn : Normal C.c (-C.s)) (h : Core C)
    (negative : C.s<0) (near : C.loU+C.side≤-C.s-(13/50)*C.c)
    (failed : -C.s-(14/25)*C.c<C.loU+C.side) :
    -1≤C.c*C.loV+C.s*(C.loU+C.side) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have sp : 0< -C.s := by linarith only [negative]
  have bands := bar_bands C cn h (-(14/25)) (by norm_num) (by norm_num)
  have low : (14/25)*C.s-C.c≤C.loV := by
    apply le_of_not_gt; intro below
    apply h.bar (-(14/25)) (by norm_num) (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bands.1,bands.2,failed,below]
  let f := (C.loV+C.c)/(-C.s)
  let u := (C.loU+C.side+C.s)/C.c
  have feq : (-C.s)*f=C.loV+C.c := by dsimp [f]; field_simp [ne_of_lt negative]
  have ueq : C.c*u=C.loU+C.side+C.s := by dsimp [u]; field_simp [ne_of_gt cp]
  have fl : -(14/25)≤f := by
    have scaled : 0≤(-C.s)*(f+14/25) := by nlinarith only [feq,low]
    have sign := nonneg_of_mul_nonneg_right scaled sp
    linarith only [sign]
  have uh : u≤-(13/50) := by
    have scaled : 0≤C.c*(-(13/50)-u) := by nlinarith only [ueq,near]
    have sign := nonneg_of_mul_nonneg_right scaled cp
    linarith only [sign]
  apply le_of_not_gt
  intro gap
  have identity : C.c*(-C.s)*(u-f)=(-C.s)*(C.loU+C.side)-C.c*C.loV-1 := by
    linear_combination (-C.s)*ueq-C.c*feq-cn.2.2
  have order : f<u := by
    have scaled : 0<C.c*(-C.s)*(u-f) := by nlinarith only [identity,gap]
    have sign := pos_of_mul_pos_right scaled (mul_pos cp sp).le
    linarith only [sign]
  let x := (f+u)/2
  have xl : -(14/25)≤x := by dsimp [x]; linarith only [fl,order]
  have xh : x≤-(13/50) := by dsimp [x]; linarith only [uh,order]
  have fy := mul_pos sp (show 0<x-f by dsimp [x]; linarith only [order])
  have yu := mul_pos cp (show 0<u-x by dsimp [x]; linarith only [order])
  have bands := bar_bands C cn h x xl xh
  apply h.bar x xl xh
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [bands.1,bands.2,feq,ueq,fy,yu]

private theorem profile_aux (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (h : Core C) (w : ℝ) (wl : 1≤w) (wh : w≤543/500)
    (missing : ¬C.Inside (-w) 0) :
    Faces C ∧ -w*C.c≤C.loU ∧ C.side≤(w-14/25)*C.c-C.s := by
  have caps := point_caps C side cn h w wl wh missing
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have sp : 0< -C.s := by linarith only [caps.2.2.2.2]
  have upperU : C.loU+C.side≤-C.s-(14/25)*C.c := by
    apply le_of_not_gt
    intro failed
    have wall := vertex C cn h caps.2.2.2.2 caps.2.2.2.1 failed
    have first := mul_le_mul_of_nonneg_left caps.2.2.1 cp.le
    have last := mul_le_mul_of_nonpos_left caps.2.1 (by linarith only [cn.1] : C.s≤0)
    have wallWeight := mul_nonneg (mul_nonneg cp.le cn.1)
      (show 0≤543/500-w by linarith only [wh])
    have sideWeight := mul_pos (sub_pos.mpr side)
      (show 0<C.c-C.s by linarith only [cp,sp])
    have margin := arc_gap cn sp
    nlinarith only [wall,first,last,wallWeight,sideWeight,margin]
  have width : C.side≤(w-14/25)*C.c-C.s := by nlinarith only [upperU,caps.2.1]
  have angle := half_width cn (show 1<(w-14/25)*C.c+(-C.s) by linarith only [side,width])
  exact ⟨⟨caps.1,upperU,caps.2.2.1,caps.2.2.2.2,angle.2⟩,caps.2.1,width⟩

/-- The wall-marker version has no preceding-origin assumption. -/
theorem weak_profile (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (h : Core C)
    (wall : ¬C.Inside (-(543/500)) 0) : WeakFaces C := by
  have data := profile_aux C side cn h (543/500) (by norm_num) (by norm_num) wall
  have width : C.side≤(263/500)*C.c-C.s := by nlinarith only [data.2.2]
  have angle := half_width cn (show 1<(263/500)*C.c+(-C.s) by linarith only [side,width])
  exact ⟨data.1,data.2.1,width,by nlinarith only [angle.1]⟩

/-- The preceding-origin version uses that literal omission instead of
the wall marker, and obtains the stronger half-angle threshold. -/
theorem strong_profile (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c (-C.s)) (h : Core C)
    (previous : ¬C.Inside (-1) 0) : StrongFaces C := by
  have data := profile_aux C side cn h 1 (by norm_num) (by norm_num) previous
  have lower : -C.c≤C.loU := by nlinarith only [data.2.1]
  have width : C.side≤(11/25)*C.c-C.s := by nlinarith only [data.2.2]
  have angle := half_width cn (show 1<(11/25)*C.c+(-C.s) by linarith only [side,width])
  exact ⟨data.1,lower,width,by nlinarith only [angle.1]⟩

#print axioms weak_profile
#print axioms strong_profile
end N12Compact.C1092MPPMMissingNegativeProfile
