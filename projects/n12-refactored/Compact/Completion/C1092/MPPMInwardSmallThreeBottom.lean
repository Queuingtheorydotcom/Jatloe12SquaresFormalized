import Compact.Completion.C1092.MPPMInwardSmallThreeBottomScalars

/-! The same physical bottom square supplies its own transverse
separator and its narrow signed orientation. Both canonical signs and
the axial contact are retained. Source only; no compiler replay. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
open C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

structure BottomProfile (C B : OpenSquare) : Prop where
  cosine : 999/1000<B.c
  low : -(43/1000)<B.s
  high : B.s<21/1000
  gamma : 0<C.c*B.s-C.s*B.c
  lambda : 24/25<C.c*B.c+C.s*B.s
  separator : B.loV+B.side≤-(C.c*B.s-C.s*B.c)*(C.loU+C.side)+
    (C.c*B.c+C.s*B.s)*C.loV

theorem bottom_profile (C B : OpenSquare) (input : BottomAngle.Input C B)
    (canonical : |B.s|≤B.c) : BottomProfile C B := by
  let c := C.c
  let s := -C.s
  let h := B.c
  let k := B.s
  let lam := c*h-s*k
  let gam := s*h+c*k
  have cn : Normal c s := input.normal
  have cb := normal_bounds cn
  have faces := BottomAngle.central_faces C B input
  have sp : 0<s := by dsimp [s]; linarith only [faces.negative]
  have small := (BottomAngle.angle C B input).2.2.le
  have bounds := small_bounds cn small
  have jb := j_bounds cn sp (BottomAngle.polynomial C B input)
  have hp : 0<h := by
    have hn := le_trans (abs_nonneg B.s) canonical
    dsimp [h]
    nlinarith only [hn,canonical,B.unit_normal,sq_abs B.s]
  have finish (gp : 0<gam) (kl : -(43/1000)<k) (ku : k<21/1000)
      (sep : B.loV+B.side≤-gam*(C.loU+C.side)+lam*C.loV) : BottomProfile C B := by
    have kSquare := mul_pos (show 0<k+43/1000 by linarith only [kl])
      (show 0<43/1000-k by linarith only [ku])
    have hh : 999/1000<h := by
      dsimp [h,k] at *
      nlinarith only [kSquare,B.unit_normal,hp,sq_nonneg (B.c-999/1000)]
    have first := mul_pos (show 0<c-97/100 by linarith only [bounds.1]) hp
    have last := mul_nonneg cn.1 (show 0≤21/1000-k by linarith only [ku])
    have lp : 24/25<lam := by
      dsimp [lam]
      nlinarith only [first,last,hh,bounds.2]
    refine ⟨hh,kl,ku,?_,?_,?_⟩
    · dsimp [gam,c,s,h,k] at gp
      nlinarith only [gp]
    · dsimp [lam,c,s,h,k] at lp
      nlinarith only [lp]
    · convert sep using 1 <;> dsimp [gam,lam,c,s,h,k] <;> ring
  by_cases positive : 0≤k
  · have bn : Normal h k := ⟨positive,by simpa only [h,k,abs_of_nonneg positive] using canonical,
      B.unit_normal⟩
    have coefficients := BottomAngle.positive_coefficients C B cn faces.negative bn
    have ln : 0≤lam := by dsimp [lam,c,s,h,k]; nlinarith only [coefficients.1]
    have gp : 0<gam := by dsimp [gam,c,s,h,k]; nlinarith only [coefficients.2]
    have sep : B.loV+B.side≤lower C (-B.s) B.c := by
      rcases BottomAngle.separators C B input canonical with central|first|last
      · exact False.elim (BottomAngle.positive_central C B input bn central)
      · have formula := lower_nn C B.c B.s lam gam
          (by dsimp [lam,c,s,h,k]; ring) (by dsimp [gam,c,s,h,k]; ring) ln gp.le
        have a := mul_nonneg ln (show 0≤-c/2-C.loU by dsimp [c]; linarith only [faces.upperLowU])
        have b := mul_nonneg gp.le (show 0≤-C.side-C.loV by linarith only [faces.upperV])
        have extra := mul_pos gp (sub_pos.mpr input.side)
        have margin := positive_source_margin cn bn small
        dsimp [lam,gam,c,s,h,k] at a b extra margin formula
        exact False.elim (by nlinarith only [first,formula,a,b,extra,margin,input.bottomMarker.2.1])
      · exact last
    have formula := lower_np C (-B.s) B.c (-gam) lam
      (by dsimp [gam,c,s,h,k]; ring) (by dsimp [lam,c,s,h,k]; ring)
      (neg_nonpos.mpr gp.le) ln
    have actual : B.loV+B.side≤-gam*(C.loU+C.side)+lam*C.loV := by rw [←formula]; exact sep
    have wall := BottomAngle.positive_wall C B input bn
    have first := mul_le_mul_of_nonneg_left faces.lowerU gp.le
    have last := mul_le_mul_of_nonneg_left faces.upperV ln
    have width : 0<lam+gam+(1+h*(h+k))/2 := by
      have p := mul_nonneg hp.le (show 0≤h+k by linarith only [hp,positive])
      nlinarith only [ln,gp,p]
    have extra := mul_pos (sub_pos.mpr input.side) width
    have identity : lam+gam+(1+h*(h+k))/2-2*h-gam*(c-(2/5)*s)=
        h*J0 c s+(1-h)^2/2+k*(h/2+c-s-c^2+(2/5)*c*s) := by
      dsimp [lam,gam,J0]; ring
    have necessary : h*J0 c s+(1-h)^2/2+k*(h/2+c-s-c^2+(2/5)*c*s)<0 := by
      dsimp [c,s,h,k] at identity ⊢
      nlinarith only [actual,wall,first,last,extra,identity]
    have high := positive_tilt cn bn small jb.1 jb.2 necessary
    exact finish gp (by linarith only [positive]) high actual
  · have negative : k<0 := lt_of_not_ge positive
    have bn : Normal h (-k) := ⟨by linarith only [negative],
      by simpa only [h,k,abs_of_neg negative] using canonical,by nlinarith only [B.unit_normal]⟩
    have coefficients := BottomAngle.negative_coefficients C B cn bn
    have lp : 0<lam := by dsimp [lam,c,s,h,k]; nlinarith only [coefficients.1]
    have height := BottomAngle.negative_wall_height C B input bn
    have sep : B.loV+B.side≤lower C (-B.s) B.c := by
      rcases BottomAngle.separators C B input canonical with central|first|last
      · exact False.elim (BottomAngle.negative_central C B input bn central)
      · have direction := BottomAngle.cone C B input B.c B.s B.unit_normal
          (by simpa only [(ownU B).2] using first)
        exact False.elim (by dsimp [k] at negative; linarith only [direction.1,negative])
      · exact last
    have gp : 0<gam := by
      apply lt_of_not_ge
      intro before
      have formula := lower_nn C (-B.s) B.c (-gam) lam
        (by dsimp [gam,c,s,h,k]; ring) (by dsimp [lam,c,s,h,k]; ring)
        (neg_nonneg.mpr before) lp.le
      have first := mul_nonneg (neg_nonneg.mpr before)
        (show 0≤-c/2-C.loU by dsimp [c]; linarith only [faces.upperLowU])
      have last := mul_nonneg lp.le (show 0≤-C.side-C.loV by linarith only [faces.upperV])
      have extra := mul_pos lp (sub_pos.mpr input.side)
      have margin := BottomAngle.negative_after_margin cn bn
        (show s*h≤c*(-k) by dsimp [gam] at before; nlinarith only [before])
      dsimp [lam,gam,c,s,h,k] at formula first last extra margin
      nlinarith only [sep,height,formula,first,last,extra,margin]
    have formula := lower_np C (-B.s) B.c (-gam) lam
      (by dsimp [gam,c,s,h,k]; ring) (by dsimp [lam,c,s,h,k]; ring)
      (neg_nonpos.mpr gp.le) lp.le
    have actual : B.loV+B.side≤-gam*(C.loU+C.side)+lam*C.loV := by rw [←formula]; exact sep
    have first := mul_le_mul_of_nonneg_left faces.lowerU gp.le
    have last := mul_le_mul_of_nonneg_left faces.upperV lp.le
    have extra := mul_pos (sub_pos.mpr input.side) (show 0<gam+lam by linarith only [gp,lp])
    have relation : lam+Q c s*gam<1 := by
      dsimp [Q,c,s]
      nlinarith only [actual,height,first,last,extra]
    have tilt := negative_tilt cn bn sp
      (show 0<s*h-c*(-k) by dsimp [gam] at gp; nlinarith only [gp])
      (show c*h+s*(-k)+Q c s*(s*h-c*(-k))<1 by
        dsimp [lam,gam] at relation; nlinarith only [relation])
    exact finish gp (by linarith only [tilt,bounds.2]) (by linarith only [negative]) actual

end
#print axioms bottom_profile
end N12Compact.C1092MPPMInwardSmallThree
