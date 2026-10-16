import Compact.Geometry.PairedCornerPositiveWall

/-! The genuine lower-V escape of a negative southeast central frame is
retained. Its full width forces the right-wall inward point, reducing this
escape to the same positive-wall lower-U displacement as the other sign. -/
namespace N12Compact.CentralRightCornerAlternatives

open S12 S12Pilot FourSquareAnchors ThreeSquare C977CornerCubic
set_option Elab.async false

private theorem canonical_bounds (B : OpenSquare) (canonical : |B.s|≤B.c) :
    0<B.c ∧ B.c≤1 := by
  have nonneg := le_trans (abs_nonneg B.s) canonical
  have signs := abs_le.mp canonical
  constructor
  · by_contra no
    have zero : B.c=0 := by linarith only [nonneg,no]
    have sine : B.s=0 := by linarith only [zero,signs.1,signs.2]
    nlinarith only [zero,sine,B.unit_normal]
  · nlinarith only [B.unit_normal,sq_nonneg B.s,sq_nonneg (B.c-1)]

/-- Both genuine corner faces survive initially, for every signed
canonical central frame. The strict central marker removes the other two. -/
theorem canonical_corner_faces (B : OpenSquare) (canonical : |B.s|≤B.c)
    (marker : B.Inside (47/20) (33/20)) (missing : ¬B.Inside 3 1) :
    B.loU+B.side≤3*B.c+B.s ∨ B.c-3*B.s≤B.loV := by
  have signs := abs_le.mp canonical
  by_cases upper : B.loU+B.side≤3*B.c+B.s
  · exact Or.inl upper
  · right
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marker.1,marker.2.2.2,upper,low,signs.1,signs.2]

/-- The real outer wall point supplies the lower V band for either
central sign. No inner auxiliary ownership is needed. -/
theorem canonical_lower_escape_point (B : OpenSquare) (canonical : |B.s|≤B.c)
    (side : 1<B.side) (marker : B.Inside (47/20) (33/20))
    (low : B.Inside 3 (87/50))
    (start : 2*(B.c+B.s)≤B.loU) (escape : B.c-3*B.s≤B.loV) : B.Inside 3 2 := by
  have b := canonical_bounds B canonical
  have signs := abs_le.mp canonical
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [marker.1,low.2.2.1,start,escape,side,signs.1,b.1,b.2]

theorem corner_faces (B : OpenSquare) (t : ℝ)
    (normal : Normal B.c t) (signed : B.s=-t)
    (marker : B.Inside (47/20) (33/20)) (missing : ¬B.Inside 3 1) :
    B.loU+B.side≤3*B.c-t ∨ B.c+3*t≤B.loV := by
  have b := normal_bounds normal
  by_cases upper : B.loU+B.side≤3*B.c-t
  · exact Or.inl upper
  · right
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marker.1,marker.2.2.2,upper,low,signed,
        normal.1,normal.2.1,b.1]

/-- Both lower-face bounds and one actual strict marker force the point.
No conditional inner auxiliary point or upper bound on the side is used. -/
theorem lower_escape_point (B : OpenSquare) (t : ℝ)
    (normal : Normal B.c t) (signed : B.s=-t) (side : 1<B.side)
    (marker : B.Inside (47/20) (33/20))
    (start : 2*(B.c-t)≤B.loU) (escape : B.c+3*t≤B.loV) : B.Inside 3 2 := by
  have b := normal_bounds normal
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [marker.1,marker.2.2.1,start,escape,side,signed,
      normal.1,normal.2.1,b.1,b.2.1]

theorem positive_wall_missing (R : OpenSquare) (normal : Normal R.c R.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (missing : ¬R.Inside 3 2) : 3*R.c+2*R.s≤R.loU := by
  have b := normal_bounds normal
  apply le_of_not_gt
  intro lower
  apply missing
  refine ⟨by nlinarith only [lower],?_,?_,?_⟩ <;>
    nlinarith only [marker.2.1,marker.2.2.1,high.2.2.2,normal.1,b.1]

/-- All signed central and right-wall frames, without conditional inner
points. The first outcome necessarily has a strictly negative central
angle; the second is the genuine neighboring positive-wall escape. -/
theorem canonical_alternatives (B R E : OpenSquare)
    (canonicalB : |B.s|≤B.c) (canonicalR : |R.s|≤R.c)
    (bSide : 1<B.side) (rSide : 1<R.side) (box : InsideContainer R)
    (bMarker : B.Inside (47/20) (33/20)) (bLow : B.Inside 3 (87/50))
    (missingCorner : ¬B.Inside 3 1)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (outward : E.Inside (16/5) 3) (corner : E.Inside 3 3)
    (right : E.Inside (1543/500) 3) (top : E.Inside 3 (1543/500))
    (br : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y))
    (er : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y))
    (start : 2*(B.c+B.s)≤B.loU) :
    (B.s<0 ∧ B.loU+B.side≤3*B.c+B.s) ∨
      (0≤R.s ∧ 3*R.c+2*R.s≤R.loU) := by
  rcases canonical_corner_faces B canonicalB bMarker missingCorner with cap | escape
  · have bound := (canonical_bounds B canonicalB).2
    exact Or.inl ⟨by linarith only [cap,start,bSide,bound],cap⟩
  · have point := canonical_lower_escape_point B canonicalB bSide bMarker bLow start escape
    have missing : ¬R.Inside 3 2 := fun h => br _ _ ⟨point,h⟩
    right
    by_cases sign : 0≤R.s
    · have rn : Normal R.c R.s :=
        ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalR,R.unit_normal⟩
      exact ⟨sign,positive_wall_missing R rn marker high missing⟩
    · have negative : R.s<0 := lt_of_not_ge sign
      have rn : Normal R.c (-R.s) :=
        ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalR,
          by nlinarith only [R.unit_normal]⟩
      exact False.elim (missing (PairedCornerPositiveWall.negative_right_point R E (-R.s)
        (by ring) rn rSide box marker high outward corner right top er))

/-- All right-wall signs are included. A negative central frame either
obeys the genuine southeast corner cap, or forces a nonnegative right
wall with its lower U face beyond the actual inward point. -/
theorem alternatives (B R E : OpenSquare) (t : ℝ)
    (bn : Normal B.c t) (signed : B.s=-t) (canonical : |R.s|≤R.c)
    (bSide : 1<B.side) (rSide : 1<R.side) (box : InsideContainer R)
    (bMarker : B.Inside (47/20) (33/20)) (missingCorner : ¬B.Inside 3 1)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (outward : E.Inside (16/5) 3) (corner : E.Inside 3 3)
    (right : E.Inside (1543/500) 3) (top : E.Inside 3 (1543/500))
    (br : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y))
    (er : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y))
    (start : 2*(B.c-t)≤B.loU) :
    B.loU+B.side≤3*B.c-t ∨ (0≤R.s ∧ 3*R.c+2*R.s≤R.loU) := by
  rcases corner_faces B t bn signed bMarker missingCorner with cap | escape
  · exact Or.inl cap
  · have point := lower_escape_point B t bn signed bSide bMarker start escape
    have missing : ¬R.Inside 3 2 := fun h => br _ _ ⟨point,h⟩
    right
    by_cases sign : 0≤R.s
    · have rn : Normal R.c R.s :=
        ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,R.unit_normal⟩
      exact ⟨sign,positive_wall_missing R rn marker high missing⟩
    · have negative : R.s<0 := lt_of_not_ge sign
      have rn : Normal R.c (-R.s) :=
        ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
          by nlinarith only [R.unit_normal]⟩
      exact False.elim (missing (PairedCornerPositiveWall.negative_right_point R E (-R.s)
        (by ring) rn rSide box marker high outward corner right top er))

#print axioms corner_faces
#print axioms canonical_corner_faces
#print axioms canonical_lower_escape_point
#print axioms canonical_alternatives
#print axioms lower_escape_point
#print axioms positive_wall_missing
#print axioms alternatives
end N12Compact.CentralRightCornerAlternatives
