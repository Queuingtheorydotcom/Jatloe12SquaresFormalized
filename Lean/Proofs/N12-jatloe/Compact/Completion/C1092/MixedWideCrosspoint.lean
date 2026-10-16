import Compact.Completion.C1092.MixedWideCrossing
import Compact.Completion.C1092.MMMP.CenterCrosspoint

/-! The second crosspoint from the true mixed wide wall. Its center cut
is nonpositive, and is retained with that direction. The same complete
support engine serves both the center and this crosspoint argument. -/
namespace N12Compact.C1092MixedWideCrosspoint
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private theorem negative (C W : OpenSquare) (c s : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (cn : Normal c s)
    (side : 1<C.side) (cap : C.side≤1001/1000) (same : C.side=W.side)
    (origin : C.Inside 0 0) (marker : C.Inside (7/20) (7/20))
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0)
    (north : ¬C.Inside (-7/20) (7/20)) (east : ¬C.Inside (7/20) (-7/20))
    (S : W.Inside (543/500) 0)
    (segment : ∀ y : ℝ, -39/100≤y → y≤2/5 → W.Inside 1 y)
    (E : ¬W.Inside 1 (-2/5))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : S12.centerY W≤0)
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
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [den.ne']
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [den.ne']
    nlinarith only [cn.2.2]
  have clt : c<1 := by nlinarith only [cn.2.2,sq_pos_of_pos sp,cp]
  have zu : z<1/2 := by
    dsimp [z]
    apply (div_lt_iff₀ den).mpr
    linarith only [cn.2.1,clt]
  have cform : (1+z^2)*c=1-z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    nlinarith only [times,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have times := congrArg (fun a : ℝ => a*z) unitAngle
    nlinarith only [times,angle]
  let rho := 1/2-z
  have rhoPos : 0<rho := by dsimp [rho]; linarith only [zu]
  have ru : c-s*rho=1-s/2 := by dsimp [rho]; nlinarith only [unitAngle]
  have rv : s+c*rho=z+c/2 := by dsimp [rho]; nlinarith only [angle]
  have deltaPos : 0<3/20-(3/10)*z+(37/20)*z^2-z^3 := by
    have first := mul_nonneg (sq_nonneg z) (show 0≤1/2-z by linarith only [zu])
    nlinarith only [first,sq_nonneg (z-1/9)]
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
  have tiny : z<1/10 := by
    apply lt_of_not_ge
    intro failure
    have bound : rho≤2/5 := by dsimp [rho]; linarith only [failure]
    exact apart 1 rho ⟨owned,segment rho (by linarith only [rhoPos]) bound⟩
  have large : 2/5<(1-z)^2/2 := by
    have product := mul_pos (sub_pos.mpr tiny)
      (show 0<19/10-z by linarith only [tiny])
    nlinarith only [product]
  have small := C1092MixedWideCrossingScalars.small c s z cp sp cn.2.1 cn.2.2
    zp zu angle sform large
  have escape : -z≤C.loU := by
    have weight := mul_nonneg zp.le (show 0≤1-c by linarith only [cb.2.1])
    nlinarith only [weight,angle,crossing]
  exact C1092MixedWideCrossing.support_impossible C W c s z rho cframe sframe
    side cap same cp sp angle unitAngle Q marker escape owned
    (by dsimp [rho]; linarith only [tiny]) zp.le
    small.1 small.2.1 small.2.2.1 small.2.2.2 S
    (segment _ (by norm_num) (by norm_num)) (segment _ (by norm_num) (by norm_num))
    E wall cut apart

theorem point (C W : OpenSquare) (side : 1<C.side) (cap : C.side≤1001/1000)
    (same : C.side=W.side) (origin : C.Inside 0 0)
    (marker : C.Inside (7/20) (7/20)) (P : C.Inside 0 (13/50))
    (Q : C.Inside (13/50) 0) (north : ¬C.Inside (-7/20) (7/20))
    (east : ¬C.Inside (7/20) (-7/20)) (S : W.Inside (543/500) 0)
    (segment : ∀ y : ℝ, -39/100≤y → y≤2/5 → W.Inside 1 y)
    (E : ¬W.Inside 1 (-2/5))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : S12.centerY W≤0)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : C.Inside 0 (1/2) := by
  obtain ⟨R,rc,range,shape,inside,_⟩ := ClosedFrames.canonical_frame C
  have sideR : 1<R.side := by simpa only [shape] using side
  have capR : R.side≤1001/1000 := by simpa only [shape] using cap
  have sameR : R.side=W.side := shape.trans same
  have o := (inside _ _).mpr origin
  have m := (inside _ _).mpr marker
  have p := (inside _ _).mpr P
  have q := (inside _ _).mpr Q
  have n : ¬R.Inside (-7/20) (7/20) := fun h => north ((inside _ _).mp h)
  have e : ¬R.Inside (7/20) (-7/20) := fun h => east ((inside _ _).mp h)
  have disjoint : ∀ x y, ¬(R.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨(inside _ _).mp h.1,h.2⟩
  apply (inside _ _).mp
  by_cases sign : 0≤R.s
  · exact C1092MMMPCenterCrosspoint.nonnegative_point R
      ⟨sign,(abs_le.mp range).2,R.unit_normal⟩ sideR o m p e
  · exact negative R W R.c (-R.s) rfl (by ring)
      ⟨by linarith only [sign],by linarith only [(abs_le.mp range).1],
        by nlinarith only [R.unit_normal]⟩ sideR capR sameR o m p q n e
      S segment E wall cut disjoint

#print axioms point
end N12Compact.C1092MixedWideCrosspoint
