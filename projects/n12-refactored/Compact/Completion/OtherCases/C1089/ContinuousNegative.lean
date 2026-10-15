import Compact.Completion.C1092.MMMP.NearCrossing
import Compact.Completion.C1092.InwardMissingProfile
import Compact.Completion.C1092.InwardCrossingConflict
import Compact.Completion.C1092.RigidCharts
import S12.Diameter

/-! The remaining negative-frame step of C1089-CONTINUOUS-REDUCTION
Theorem 3. The small side needed for an existing global-coordinate API
is derived from C's actual missing-center profile. The other three walls
of the translated B then follow from its strict marker and diameter;
only the manuscript's genuine one-sided B wall is assumed.
Source translation only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousNegative
open S12 S12Pilot C1092RigidCharts C977CornerCubic
set_option Elab.async false

private theorem right_box (R : OpenSquare) (small : R.side≤7/5)
    (wall : ∀ x y,R.Inside x y → x≤4)
    (marker : R.Inside (1543/500) 2) : InsideContainer R := by
  have square : R.side^2≤49/25 := by
    have product := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤7/5+R.side by linarith only [R.side_pos])
    nlinarith only [product]
  intro x y own
  have distance := inside_distance_bound R x y (1543/500) 2 own marker
  have dx : (x-1543/500)^2<4 := by
    nlinarith only [distance,square,sq_nonneg (y-2)]
  have dy : (y-2)^2<4 := by
    nlinarith only [distance,square,sq_nonneg (x-1543/500)]
  have left : -2<x-1543/500 := by
    by_contra failure
    have bound : x-1543/500≤ -2 := le_of_not_gt failure
    nlinarith only [dx,bound,sq_nonneg (x-1543/500+2)]
  exact ⟨by linarith only [left],wall _ _ own,
    by nlinarith only [dy,sq_nonneg y],
    by nlinarith only [dy,sq_nonneg (y-4)]⟩

/-- Once both outer anchors and the center are absent, the genuine
neighbor W forces a crossing, and the same actual B rules it out. -/
theorem impossible (C W B : OpenSquare) (side : 1<C.side)
    (sameW : C.side=W.side) (sameB : C.side=B.side)
    (cp : 0<C.c) (sn : C.s≤0) (order : -C.s≤C.c)
    (M : C.Inside (7/20) (7/20)) (P : C.Inside 0 (13/50))
    (Q : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (R : ¬C.Inside 1 (2/5)) (A : ¬C.Inside (2/5) 1)
    (N : ¬C.Inside (-7/20) (7/20))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (near : W.Inside 1 (39/100))
    (wallW : ∀ x y,W.Inside x y → x≤2) (cutW : 0≤centerY W)
    (wallB : ∀ x y,B.Inside x y → y≤2)
    (markerB : B.Inside 0 (543/500)) (innerB : B.Inside (2/5) 1)
    (apartW : ∀ x y,¬(C.Inside x y ∧ W.Inside x y))
    (apartB : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : False := by
  have profile := C1092InwardMissingProfile.profile C side cp sn order M P Q O R A N
  have cn : Normal C.c (-C.s) :=
    ⟨by linarith only [sn],order,by nlinarith only [C.unit_normal]⟩
  have bounds := normal_bounds cn
  have smallSide : C.side≤7/5 := by
    linarith only [profile.lowerV,profile.upperV,bounds.2.1,bounds.2.2.2.1]
  let z := C1092WallProfileScalars.half C.c (-C.s)
  have denominator : 0<1+C.c := by linarith only [cp]
  have zn : 0≤z := by
    dsimp only [z,C1092WallProfileScalars.half]
    exact div_nonneg (by linarith only [profile.sine]) denominator.le
  have angle : z*(1+C.c)=-C.s := by
    dsimp only [z,C1092WallProfileScalars.half]
    field_simp [denominator.ne']
  have unitAngle : (-C.s)*z=1-C.c := by
    dsimp only [z,C1092WallProfileScalars.half]
    field_simp [denominator.ne']
    nlinarith only [C.unit_normal]
  have crossing := C1092MMMPNearCrossing.point C W C.c (-C.s) rfl (by ring) cn
    side sameW profile.lowerV P Q S T near wallW cutW apartW
  let E := translate (swap C) (-2) (-2)
  let D := translate (swap B) (-2) (-2)
  have chart (X : OpenSquare) (x y : ℝ) :
      (translate (swap X) (-2) (-2)).Inside x y↔X.Inside (y-2) (x-2) := by
    rw [inside_translate,inside_swap]
    congr 2 <;> ring
  have markerD : D.Inside (1543/500) 2 := by
    change (translate (swap B) (-2) (-2)).Inside _ _
    norm_num [chart]
    exact markerB
  have box : InsideContainer D := right_box D (by simpa only [D,translate,swap,←sameB] using smallSide)
    (by
      intro x y own
      have bound := wallB _ _ ((chart B _ _).mp own)
      linarith only [bound]) markerD
  have escape : 2*E.c+2*E.s≤E.loU := by
    dsimp only [E,translate,swap]
    linarith only [profile.lowerV]
  have floor : -(47/20)*E.s+(33/20)*E.c≤E.loV := by
    dsimp only [E,translate,swap]
    linarith only [profile.lowerU]
  exact C1092InwardCrossingConflict.impossible E D side sameB cp
    (by dsimp only [E,translate,swap]; linarith only [profile.sine]) escape floor
    (by change (translate (swap C) (-2) (-2)).Inside _ _; norm_num [chart]; exact P)
    (by change (translate (swap C) (-2) (-2)).Inside _ _; norm_num [chart]; exact profile.outer)
    z zn profile.halfSmall
    (by simpa only [E,translate,swap,mul_comm] using angle)
    (by simpa only [E,translate,swap] using unitAngle)
    (by
      change (translate (swap C) (-2) (-2)).Inside _ _
      rw [chart]
      convert crossing using 1 <;> dsimp only [z,C1092WallProfileScalars.half] <;> ring)
    box markerD
    (by change (translate (swap B) (-2) (-2)).Inside _ _; norm_num [chart]; exact innerB)
    (by
      intro x y own
      exact apartB _ _ ⟨(chart C _ _).mp own.1,(chart B _ _).mp own.2⟩)

#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.ContinuousNegative
