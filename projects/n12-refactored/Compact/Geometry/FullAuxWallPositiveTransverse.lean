import Compact.Geometry.FullAuxWallPositiveReach

/-! All signed outer-square frames share this actual SAT reduction.
The shifted owned point is supplied by FullAuxWallPositiveReach, not by
a saved enclosure or a positive-orientation assumption on B. -/
namespace N12Compact.FullAuxWallPositiveTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic
set_option Elab.async false

theorem alternatives (D B : OpenSquare)
    (dn : Normal D.c D.s) (bc : 0<B.c)
    (lowerSign : -B.c≤B.s) (upperSign : B.s≤B.c)
    (same : D.side=B.side)
    (center : D.Inside 2 2) (left : D.Inside (6/5) (19/10))
    (southwest : D.Inside (33/20) (33/20))
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) :
    D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV := by
  have db := normal_bounds dn
  have dc : 0<D.c := by linarith only [db.1]
  have noDU (h : upper D D.c D.s≤lower B D.c D.s ∨
      upper B D.c D.s≤lower D D.c D.s) : False := by
    have p := strict_bounds D _ _ D.c D.s D.unit_normal center
    have l := strict_bounds D _ _ D.c D.s D.unit_normal left
    have m := strict_bounds B _ _ D.c D.s D.unit_normal marker
    rcases h with h | h <;>
      nlinarith only [h,p.2,l.1,m.1,m.2,dc,dn.1,dn.2.1]
  have noBU (h : upper D B.c B.s≤lower B B.c B.s ∨
      upper B B.c B.s≤lower D B.c B.s) : False := by
    have p := strict_bounds D _ _ B.c B.s B.unit_normal center
    have l := strict_bounds D _ _ B.c B.s B.unit_normal left
    have m := strict_bounds B _ _ B.c B.s B.unit_normal marker
    have f := strict_bounds B _ _ B.c B.s B.unit_normal high
    rcases h with h | h <;>
      nlinarith only [h,p.2,l.1,m.2,f.1,bc,lowerSign,upperSign]
  have forward (x y : ℝ) (yp : 0<y) (unit : x^2+y^2=1)
      (h : upper D x y≤lower B x y ∨ upper B x y≤lower D x y) :
      upper D x y≤lower B x y := by
    rcases h with h | h
    · exact h
    · have p := (strict_bounds D _ _ x y unit southwest).1
      have m := (strict_bounds B _ _ x y unit marker).2
      exfalso
      nlinarith only [h,p,m,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint D B same apart
  change pairRadius D B≤|D.c*(centerX B-centerX D)+D.s*(centerY B-centerY D)| ∨
    pairRadius D B≤|-D.s*(centerX B-centerX D)+D.c*(centerY B-centerY D)| ∨
    pairRadius B D≤|B.c*(centerX B-centerX D)+B.s*(centerY B-centerY D)| ∨
    pairRadius B D≤|-B.s*(centerX B-centerX D)+B.c*(centerY B-centerY D)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius D x y+supportRadius B x y=R)
      (h : R≤|x*(centerX B-centerX D)+y*(centerY B-centerY D)|) :=
    separated D B x y (by rwa [identity])
  rcases axes with du | dv | bu | bv
  · exact False.elim (noDU (separateAxis _ _ _ (parallel_radius D B) du))
  · have unit : (-D.s)^2+D.c^2=1 := by nlinarith only [D.unit_normal]
    have h := forward _ _ dc unit (separateAxis _ _ _ (transverse_radius D B) dv)
    left
    simpa only [(ownV D).2] using h
  · have identity : supportRadius D B.c B.s+supportRadius B B.c B.s=pairRadius B D := by
      rw [add_comm]
      exact parallel_radius B D
    exact False.elim (noBU (separateAxis _ _ _ identity bu))
  · have identity : supportRadius D (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B D := by
      rw [add_comm]
      exact transverse_radius B D
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have h := forward _ _ bc unit (separateAxis _ _ _ identity bv)
    right
    simpa only [(ownV B).1] using h

#print axioms alternatives
end N12Compact.FullAuxWallPositiveTransverse
