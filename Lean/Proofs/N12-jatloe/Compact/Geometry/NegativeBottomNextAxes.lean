import Compact.Geometry.NegativeBottomInnerWall
import Compact.Geometry.C696BottomChainSelectors
import Compact.Geometry.OwnedWestBottomAngle

/-! The original missing-corner negative singleton has two genuine
marker faces. The upper-U face is shallow; the other is uniformly steep.
When the next wall is also negative, its intrinsic inner point removes
both longitudinal separators and leaves exactly two upward axes. -/
namespace N12Compact.NegativeBottomNextAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem marker_escape (O : OpenSquare) (s : ℝ) (os : O.s=-s)
    (on : Normal O.c s) (side : 1<O.side)
    (marker : O.Inside 1 (457/500))
    (missing : ¬O.Inside 2 (457/500))
    (corner : O.c-s≤O.loU) (face : boundary O.c s<O.loV+O.side) :
    s<1/5 ∨ (47/100<s ∧ 27/20<O.c+s) := by
  have ob := normal_bounds on
  have cp : 0<O.c := by linarith only [ob.1]
  have escape : O.loU+O.side≤2*O.c-(457/500)*s ∨
      O.loV+O.side≤2*s+(457/500)*O.c := by
    by_cases upperU : O.loU+O.side≤2*O.c-(457/500)*s
    · exact Or.inl upperU
    · right
      apply le_of_not_gt
      intro upperV
      apply missing
      apply (negative_bands O s 2 (457/500) os).mpr
      have marked := (negative_bands O s 1 (457/500) os).mp marker
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [marked.1,marked.2.2.1,cp,on.1,upperU,upperV]
  rcases escape with upperU | upperV
  · left
    have chord : 1-O.c<(43/500)*s := by linarith only [corner,upperU,side]
    have positive : 0<s := by nlinarith only [chord,ob.2.1]
    have weighted := mul_lt_mul_of_pos_left chord
      (show 0<1+O.c by linarith only [cp])
    have replace := mul_nonneg on.1 (sub_nonneg.mpr ob.2.1)
    have square : s^2<(43/250)*s := by nlinarith only [weighted,replace,on.2.2]
    have product : 0<s*(43/250-s) := by nlinarith only [square]
    have gap := pos_of_mul_pos_right product positive.le
    linarith only [gap]
  · exact Or.inr (OwnedWestBottomAngle.upper_v_spread on (lt_of_lt_of_le face upperV))

/-- The next negative wall owns its true inner point. The negative
singleton passes beyond that point on every negative longitudinal axis,
so only the two forward transverse axes can separate the pair. -/
theorem negative_wall (O D : OpenSquare) (s r : ℝ)
    (os : O.s=-s) (ds : D.s=-r)
    (on : Normal O.c s) (dn : Normal D.c r)
    (same : O.side=D.side) (side : 1<O.side)
    (corner : O.c-s≤O.loU) (floor : s*(O.loU+O.side)≤O.c*O.loV)
    (oMarker : O.Inside 1 (457/500)) (oMiddle : O.Inside (87/50) 1)
    (oFar : O.Inside (187/100) (19/25))
    (dMarker : D.Inside 2 (457/500)) (dInner : D.Inside 2 1)
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) :
    O.loV+O.side≤lower D s O.c ∨ upper O r D.c≤D.loV := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have axes := C696BottomChainSelectors.singleton_wall O D oc dc
    (by rw [os]; linarith only [on.1,oc])
    (by rw [ds]; linarith only [dn.1,dc]) same oMarker oMiddle oFar dMarker apart
  have ownProjection := NegativeBottomInnerWall.negative_projection O s O.c s
    os on on side corner floor oMarker
  have nextProjection := NegativeBottomInnerWall.negative_projection O s D.c r
    os on dn side corner floor oMarker
  rcases axes with first | last
  · rcases first with longitudinal | transverse
    · have point := (strict_bounds D _ _ O.c (-s)
        (by nlinarith only [on.2.2]) dInner).1
      rw [os] at longitudinal
      exact False.elim (by linarith only [ownProjection,point,longitudinal])
    · left
      have h := transverse.2
      rw [(ownV O).2] at h
      simpa only [os,neg_neg] using h
  · rcases last with longitudinal | transverse
    · have point := (strict_bounds D _ _ D.c (-r)
        (by nlinarith only [dn.2.2]) dInner).1
      rw [ds] at longitudinal
      exact False.elim (by linarith only [nextProjection,point,longitudinal])
    · right
      have h := transverse.2
      rw [(ownV D).1] at h
      simpa only [ds,neg_neg] using h

/-- On the genuine steep marker face, a positive next wall retains
only the singleton's upward axis and the wall's rightward axis. The
singleton's U axis would force the already excluded shallow face. -/
theorem positive_wall (O D : OpenSquare) (s : ℝ) (os : O.s=-s)
    (on : Normal O.c s) (dn : Normal D.c D.s)
    (same : O.side=D.side) (side : 1<O.side) (steep : 47/100<s)
    (corner : O.c-s≤O.loU)
    (oMarker : O.Inside 1 (457/500)) (oMiddle : O.Inside (87/50) 1)
    (oFar : O.Inside (187/100) (19/25)) (dMarker : D.Inside 2 (457/500))
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) :
    O.loV+O.side≤lower D s O.c ∨ upper O D.c D.s≤D.loU := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have sine : s≤5/7 := by linarith only [on.2.1,ob.2.2.2.2.2]
  have square := mul_nonneg (show 0≤s-47/100 by linarith only [steep])
    (show 0≤s+47/100 by linarith only [on.1])
  have narrow : O.c≤9/10 := by
    by_contra failure
    have product := mul_nonneg (show 0≤O.c-9/10 by linarith only [failure])
      (show 0≤O.c+9/10 by linarith only [oc])
    nlinarith only [product,square,on.2.2]
  have axes := C696BottomChainSelectors.singleton_wall O D oc dc
    (by rw [os]; linarith only [on.1,oc]) dn.2.1 same
    oMarker oMiddle oFar dMarker apart
  rcases axes with first | last
  · rcases first with longitudinal | transverse
    · have point := (strict_bounds D _ _ O.c (-s)
        (by nlinarith only [on.2.2]) dMarker).1
      rw [(ownU O).2,os] at longitudinal
      exact False.elim (by nlinarith only [point,longitudinal,corner,side,narrow,sine])
    · left
      have h := transverse.2
      rw [(ownV O).2] at h
      simpa only [os,neg_neg] using h
  · rcases last with longitudinal | transverse
    · exact Or.inr (by simpa only [(ownU D).1] using longitudinal)
    · exact False.elim (by nlinarith only [transverse.1,dn.1,dc])

#print axioms marker_escape
#print axioms negative_wall
#print axioms positive_wall
end N12Compact.NegativeBottomNextAxes
