import Compact.Completion.C1092.MMMP.CenterCrosspointSupport

/-! A center-to-crosspoint theorem for two original physical squares.
The complete wall square, its genuine wall, its center sign and its whole
strict segment are retained. All central and wall orientations are covered. -/
namespace N12Compact.C1092MMMPCenterCrosspoint
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

theorem nonnegative_point (C : OpenSquare) (cn : Normal C.c C.s) (side : 1<C.side)
    (origin : C.Inside 0 0) (marker : C.Inside (7/20) (7/20))
    (P : C.Inside 0 (13/50)) (missing : ¬C.Inside (7/20) (-7/20)) :
    C.Inside 0 (1/2) := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have faces : -(7/20)*(C.c+C.s)≤C.loV := by
    apply le_of_not_gt
    intro failure
    apply missing
    dsimp [OpenSquare.Inside,InBands] at origin marker ⊢
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,origin.1,origin.2.2.2,marker.2.1,cp,cn.1,cn.2.1]
  have short : (17/20)*C.c+(7/20)*C.s<1 := by
    nlinarith only [cn.2.2,sq_nonneg ((7/20)*C.c-(17/20)*C.s),
      sq_nonneg ((17/20)*C.c+(7/20)*C.s-1)]
  dsimp [OpenSquare.Inside,InBands] at origin marker P ⊢
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [origin.1,marker.2.1,P.2.2.1,faces,short,side,cp,cn.1,cn.2.1]

private theorem negative (C W : OpenSquare) (c s : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (cn : Normal c s)
    (side : 1<C.side) (same : C.side=W.side)
    (origin : C.Inside 0 0) (marker : C.Inside (7/20) (7/20))
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0)
    (north : ¬C.Inside (-7/20) (7/20)) (east : ¬C.Inside (7/20) (-7/20))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (segment : ∀ y : ℝ, 0≤y → y≤39/100 → W.Inside 1 y)
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : C.Inside 0 (1/2) := by
  classical
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have o : C.loU<0 ∧ 0<C.loU+C.side ∧ C.loV<0 ∧ 0<C.loV+C.side := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using origin
  have m := marker
  have p := P
  dsimp [OpenSquare.Inside,InBands] at m p
  rw [cframe,sframe] at m p
  have lowerU : -(7/20)*(c+s)≤C.loU := by
    apply le_of_not_gt
    intro failure
    apply north
    dsimp [OpenSquare.Inside,InBands]
    rw [cframe,sframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,o.2.1,o.2.2.1,m.2.2.2,cp,cn.1,cn.2.1]
  have lowerV : -(7/20)*(c-s)≤C.loV := by
    apply le_of_not_gt
    intro failure
    apply east
    dsimp [OpenSquare.Inside,InBands]
    rw [cframe,sframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,o.1,o.2.2.2,lowerU,side,cp,cn.1,cn.2.1,cb.2.2.2.2.2]
  by_contra missing
  have crossing : -s/2≤C.loU := by
    apply le_of_not_gt
    intro failure
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    rw [cframe,sframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,m.2.1,p.2.2.1,lowerV,side,cp,cn.1,cn.2.1,cb.2.1]
  have sp : 0<s := by linarith only [crossing,o.1,cn.1]
  let z := s/(1+c)
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [ne_of_gt den]
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [ne_of_gt den]
    nlinarith only [cn.2.2]
  have clt : c<1 := by nlinarith only [cn.2.2,sq_pos_of_pos sp,cp]
  have zu : z<1/2 := by
    dsimp [z]
    apply (div_lt_iff₀ den).mpr
    linarith only [cn.2.1,clt]
  have cform : (1+z^2)*c=1-z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    dsimp at times
    nlinarith only [times,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have times := congrArg (fun a : ℝ => a*z) unitAngle
    dsimp at times
    nlinarith only [times,angle]
  let rho := 1/2-z
  have rhoPos : 0<rho := by dsimp [rho]; linarith only [zu]
  have ru : c-s*rho=1-s/2 := by dsimp [rho]; nlinarith only [unitAngle]
  have rv : s+c*rho=z+c/2 := by dsimp [rho]; nlinarith only [angle]
  have deltaPos : 0<3/20-(3/10)*z+(37/20)*z^2-z^3 := by
    have first := mul_nonneg (sq_nonneg z) (show 0≤1/2-z by linarith only [zu])
    have last := sq_nonneg (z-1/9)
    nlinarith only [first,last]
  have deltaIdentity : (1+z^2)*(1-z-(17/20)*c+(7/20)*s)=
      3/20-(3/10)*z+(37/20)*z^2-z^3 := by
    linear_combination -(17/20)*cform+(7/20)*sform
  have short : z+(17/20)*c-(7/20)*s<1 := by
    apply lt_of_not_ge
    intro failure
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+z^2 by positivity)
      (show 1-z-(17/20)*c+(7/20)*s≤0 by linarith only [failure])
    linarith only [deltaIdentity,deltaPos,product]
  have owned : C.Inside 1 rho := by
    dsimp [OpenSquare.Inside,InBands]
    rw [cframe,sframe]
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [ru,o.1,cb.2.2.2.1]
    · nlinarith only [ru,crossing,side]
    · nlinarith only [rv,o.2.2.1,zp,cp]
    · nlinarith only [rv,short,lowerV,side]
  have tiny : z<11/100 := by
    apply lt_of_not_ge
    intro failure
    have bound : rho≤39/100 := by dsimp [rho]; linarith only [failure]
    exact apart 1 rho ⟨owned,segment rho rhoPos.le bound⟩
  have small : s≤1/4 := by
    have product := mul_nonneg zp.le (show 0≤1-c by linarith only [cb.2.1])
    nlinarith only [angle,product,tiny]
  have large : 13/50<rho := by dsimp [rho]; linarith only [tiny]
  exact C1092MMMPCenterCrosspointSupport.impossible C W c s cframe sframe cn sp small
    side same crossing lowerV o.2.2.1 Q rho large owned S T wall cut apart

/-- The entire signed canonical cover is used. No center premise on C is
inferred from the listed marker points; its strict origin is explicit. -/
theorem point (C W : OpenSquare) (side : 1<C.side) (same : C.side=W.side)
    (origin : C.Inside 0 0) (marker : C.Inside (7/20) (7/20))
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0)
    (north : ¬C.Inside (-7/20) (7/20)) (east : ¬C.Inside (7/20) (-7/20))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (segment : ∀ y : ℝ, 0≤y → y≤39/100 → W.Inside 1 y)
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : C.Inside 0 (1/2) := by
  classical
  obtain ⟨R,rc,rs,rside,rinside,_⟩ := ClosedFrames.canonical_frame C
  have ha : 1<R.side := by rwa [rside]
  have result : R.Inside 0 (1/2) := by
    by_cases sign : 0≤R.s
    · have cn : Normal R.c R.s := ⟨sign,by simpa only [abs_of_nonneg sign] using rs,R.unit_normal⟩
      exact nonnegative_point R cn ha ((rinside _ _).mpr origin) ((rinside _ _).mpr marker)
        ((rinside _ _).mpr P) (fun own => east ((rinside _ _).mp own))
    · have sn : R.s≤0 := by exact (lt_of_not_ge sign).le
      have cn : Normal R.c (-R.s) := ⟨by linarith only [sn],
        by simpa only [abs_of_nonpos sn] using rs,by nlinarith only [R.unit_normal]⟩
      exact negative R W R.c (-R.s) rfl (by ring) cn ha (rside.trans same)
        ((rinside _ _).mpr origin) ((rinside _ _).mpr marker)
        ((rinside _ _).mpr P) ((rinside _ _).mpr Q)
        (fun own => north ((rinside _ _).mp own)) (fun own => east ((rinside _ _).mp own))
        S T segment wall cut (fun x y own => apart x y ⟨(rinside _ _).mp own.1,own.2⟩)
  exact (rinside _ _).mp result

#print axioms point
end N12Compact.C1092MMMPCenterCrosspoint
