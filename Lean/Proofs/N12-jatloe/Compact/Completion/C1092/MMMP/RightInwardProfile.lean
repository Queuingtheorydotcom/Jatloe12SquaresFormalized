import Compact.Geometry.ClosedFrames
import Compact.Geometry.C977CornerCubic

/-! The original right wall owning its inward G-point has a negative
canonical frame with exact strict slope bounds. No wall or side cap is
used in this local forced-face argument. -/
namespace N12Compact.C1092MMMPRightInwardProfile
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure Data (R : OpenSquare) : Prop where
  lowerU : (7/20)*(R.c+R.s)≤R.loU
  lowerV : -R.s-(13/50)*R.c≤R.loV
  lowerSlope : 9*R.c<35*(-R.s)
  upperSlope : 37*(-R.s)<13*R.c
  cosine : 47/50<R.c
  sineLow : 6/25 < -R.s
  sineHigh : -R.s<1/3

private theorem positive_impossible (R : OpenSquare) (rn : Normal R.c R.s)
    (side : 1<R.side) (A : R.Inside (13/50) 0)
    (S : R.Inside (543/500) 0) (D : R.Inside 1 (2/5))
    (F : ¬R.Inside 1 (-13/50)) (M : ¬R.Inside (7/20) (7/20)) : False := by
  have rb := normal_bounds rn
  have rp : 0<R.c := by linarith only [rb.1]
  have lower : -R.s-(13/50)*R.c≤R.loV := by
    apply le_of_not_gt
    intro failure
    apply F
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,A.1,S.2.1,A.2.2.2,rp,rn.1,rn.2.1]
  have upper : R.loV+R.side≤(7/20)*(R.c-R.s) := by
    apply le_of_not_gt
    intro failure
    apply M
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,A.1,S.2.1,A.2.2.1,rp,rn.1,rn.2.1]
  have short : (61/100)*R.c+(13/20)*R.s<1 := by
    nlinarith only [rn.2.2,sq_nonneg ((13/20)*R.c-(61/100)*R.s),
      sq_nonneg ((61/100)*R.c+(13/20)*R.s-1)]
  linarith only [lower,upper,side,short]

theorem negative_data (R : OpenSquare) (rn : Normal R.c (-R.s))
    (side : 1<R.side) (A : R.Inside (13/50) 0)
    (S : R.Inside (543/500) 0) (D : R.Inside 1 (2/5))
    (F : ¬R.Inside 1 (-13/50)) (M : ¬R.Inside (7/20) (7/20)) : Data R := by
  have rb := normal_bounds rn
  have rp : 0<R.c := by linarith only [rb.1]
  have lowerU : (7/20)*(R.c+R.s)≤R.loU := by
    apply le_of_not_gt
    intro failure
    apply M
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,S.2.1,A.2.2.1,D.2.2.2,rp,rn.1,rn.2.1]
  have short : (13/20)*R.c+(61/100)*(-R.s)<1 := by
    nlinarith only [rn.2.2,sq_nonneg ((61/100)*R.c-(13/20)*(-R.s)),
      sq_nonneg ((13/20)*R.c+(61/100)*(-R.s)-1)]
  have lowerV : -R.s-(13/50)*R.c≤R.loV := by
    apply le_of_not_gt
    intro failure
    have upperU : R.c-(13/50)*R.s<R.loU+R.side := by
      linarith only [lowerU,short,side]
    apply F
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,upperU,A.1,D.2.2.2,rp,rn.1,rn.2.1]
  have slopeLow : 9*R.c<35*(-R.s) := by linarith only [lowerU,A.1]
  have slopeHigh : 37*(-R.s)<13*R.c := by linarith only [lowerV,A.2.2.1]
  have sector := mul_pos (show 0<13*R.c-37*(-R.s) by linarith only [slopeHigh])
    (show 0<13*R.c+37*(-R.s) by linarith only [rp,rn.1])
  have cosine : 47/50<R.c := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤47/50-R.c by linarith only [bad])
      (show 0≤47/50+R.c by linarith only [rp])
    nlinarith only [sector,product,rn.2.2]
  have sineLow : 6/25 < -R.s := by linarith only [slopeLow,cosine]
  have sineHigh : -R.s<1/3 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤-R.s-1/3 by linarith only [bad])
      (show 0≤-R.s+1/3 by linarith only [rn.1])
    nlinarith only [sector,product,rn.2.2]
  exact ⟨lowerU,lowerV,slopeLow,slopeHigh,cosine,sineLow,sineHigh⟩

theorem exists_negative (W : OpenSquare) (side : 1<W.side)
    (A : W.Inside (13/50) 0) (S : W.Inside (543/500) 0) (D : W.Inside 1 (2/5))
    (F : ¬W.Inside 1 (-13/50)) (M : ¬W.Inside (7/20) (7/20)) :
    ∃ R : OpenSquare, R.side=W.side ∧ (∀ x y, R.Inside x y↔W.Inside x y) ∧
      Normal R.c (-R.s) ∧ Data R := by
  classical
  obtain ⟨R,rc,rs,rside,rinside,_⟩ := ClosedFrames.canonical_frame W
  have ha : 1<R.side := by rwa [rside]
  have a := (rinside _ _).mpr A
  have s := (rinside _ _).mpr S
  have d := (rinside _ _).mpr D
  have f : ¬R.Inside 1 (-13/50) := fun own => F ((rinside _ _).mp own)
  have m : ¬R.Inside (7/20) (7/20) := fun own => M ((rinside _ _).mp own)
  have sign : R.s≤0 := by
    apply le_of_not_gt
    intro positive
    have rn : Normal R.c R.s := ⟨positive.le,by simpa only [abs_of_pos positive] using rs,R.unit_normal⟩
    exact positive_impossible R rn ha a s d f m
  have rn : Normal R.c (-R.s) := ⟨by linarith only [sign],
    by simpa only [abs_of_nonpos sign] using rs,by nlinarith only [R.unit_normal]⟩
  exact ⟨R,rside,rinside,rn,negative_data R rn ha a s d f m⟩

#print axioms negative_data
#print axioms exists_negative
end N12Compact.C1092MMMPRightInwardProfile
