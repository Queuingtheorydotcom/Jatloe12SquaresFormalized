import Compact.Geometry.ABTransverse

/-! Actual southwest versus a positive southeast square.  The west
and south crosspoints remove both southeast transverse axes without a
center premise.  The remaining southwest transverse separator retains
its necessary strict negative-angle bound.  All weak SAT contacts remain. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem positive_southeast_alternatives (A E : OpenSquare)
    (ac : 0<A.c) (canonical : |A.s|≤A.c)
    (ec : 0<E.c) (es : 0≤E.s) (orderE : E.s≤E.c)
    (same : A.side=E.side)
    (west : A.Inside (-1/2) 0) (south : A.Inside 0 (-1/2))
    (nearA : A.Inside 0 (-13/50))
    (markerE : E.Inside (7/20) (-7/20))
    (outerE : E.Inside 1 (-13/50)) (innerE : E.Inside (13/50) 0)
    (apart : ∀ x y,¬(A.Inside x y ∧ E.Inside x y)) :
    A.loU+A.side≤lower E A.c A.s ∨
      upper A E.c E.s≤E.loU ∨
      (17*A.s< -7*A.c ∧ A.loV+A.side≤lower E (-A.s) A.c) := by
  have forwardU (c s : ℝ) (positive : 0<c) (unit : c^2+s^2=1)
      (sep : upper A c s≤lower E c s ∨ upper E c s≤lower A c s) :
      upper A c s≤lower E c s := by
    rcases sep with forward | backward
    · exact forward
    · have first := strict_bounds A _ _ c s unit nearA
      have last := strict_bounds E _ _ c s unit outerE
      exfalso
      linarith only [backward,first.1,last.2,positive]
  have transverse (c s : ℝ) (positive : 0<c) (order : s≤c)
      (unit : c^2+s^2=1)
      (sep : upper A (-s) c≤lower E (-s) c ∨
        upper E (-s) c≤lower A (-s) c) :
      17*s< -7*c ∧ upper A (-s) c≤lower E (-s) c := by
    have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
    rcases sep with forward | backward
    · have first := strict_bounds A _ _ (-s) c normal west
      have last := strict_bounds E _ _ (-s) c normal markerE
      exact ⟨by linarith only [first.2,last.1,forward],forward⟩
    · have first := strict_bounds A _ _ (-s) c normal south
      have last := strict_bounds E _ _ (-s) c normal innerE
      exfalso
      linarith only [first.1,last.2,backward,positive,order]
  have axes := CongruentSAT.faceSeparation_of_disjoint A E same apart
  change pairRadius A E≤|A.c*(centerX E-centerX A)+A.s*(centerY E-centerY A)| ∨
    pairRadius A E≤|-A.s*(centerX E-centerX A)+A.c*(centerY E-centerY A)| ∨
    pairRadius E A≤|E.c*(centerX E-centerX A)+E.s*(centerY E-centerY A)| ∨
    pairRadius E A≤|-E.s*(centerX E-centerX A)+E.c*(centerY E-centerY A)| at axes
  have separate (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius E nx ny=radius)
      (axis : radius≤|nx*(centerX E-centerX A)+ny*(centerY E-centerY A)|) :=
    separated A E nx ny (by rwa [identity])
  rcases axes with au | av | eu | ev
  · left
    have result := forwardU A.c A.s ac A.unit_normal
      (separate _ _ _ (parallel_radius A E) au)
    simpa only [(ownU A).2] using result
  · right; right
    have result := transverse A.c A.s ac (abs_le.mp canonical).2 A.unit_normal
      (separate _ _ _ (transverse_radius A E) av)
    exact ⟨result.1,by simpa only [(ownV A).2] using result.2⟩
  · right; left
    have identity : supportRadius A E.c E.s+supportRadius E E.c E.s=pairRadius E A := by
      rw [add_comm]
      exact parallel_radius E A
    have result := forwardU E.c E.s ec E.unit_normal (separate _ _ _ identity eu)
    simpa only [(ownU E).1] using result
  · have identity : supportRadius A (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E A := by
      rw [add_comm]
      exact transverse_radius E A
    have result := transverse E.c E.s ec orderE E.unit_normal (separate _ _ _ identity ev)
    exact False.elim (by linarith only [result.1,ec,es])

/-- At a nonnegative SW frame only the two actual longitudinal axes
remain.  The zero angle is included in the discarded transverse mode. -/
theorem nonnegative_pair_alternatives (A E : OpenSquare)
    (ac : 0<A.c) (aSign : 0≤A.s) (canonical : |A.s|≤A.c)
    (ec : 0<E.c) (es : 0≤E.s) (orderE : E.s≤E.c)
    (same : A.side=E.side)
    (west : A.Inside (-1/2) 0) (south : A.Inside 0 (-1/2))
    (nearA : A.Inside 0 (-13/50))
    (markerE : E.Inside (7/20) (-7/20))
    (outerE : E.Inside 1 (-13/50)) (innerE : E.Inside (13/50) 0)
    (apart : ∀ x y,¬(A.Inside x y ∧ E.Inside x y)) :
    A.loU+A.side≤lower E A.c A.s ∨ upper A E.c E.s≤E.loU := by
  rcases positive_southeast_alternatives A E ac canonical ec es orderE same
      west south nearA markerE outerE innerE apart with first | second | third
  · exact Or.inl first
  · exact Or.inr second
  · exact False.elim (by linarith only [third.1,ac,aSign])

#print axioms positive_southeast_alternatives
#print axioms nonnegative_pair_alternatives
end N12Compact.FiniteCases.C972Local
