import Compact.Geometry.ABTransverse

/-! The proposed outer reach of the actual northeast corner retains the
foreign right-wall point. Without that exclusion the two-square statement
is false. Its negation removes one complete separating-axis choice. -/
namespace N12Compact.UpperRightCornerReachAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse

/-- A positive corner which misses the farther row point must put the
genuine right-wall point below its lower transverse face. The competing
longitudinal escape would leave less than one unit of complete side. -/
theorem lower_face (E : OpenSquare)
    (positive : 0<E.c) (sign : 0≤E.s) (canonical : E.s≤E.c)
    (side : 1<E.side) (corner : E.Inside 3 3)
    (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (missingReach : ¬E.Inside (7/2) 3) :
    (12/5)*E.c-3*E.s≤E.loV := by
  have short : (1/2)*E.c+(3/5)*E.s<1 := by
    have cauchy : ((1/2)*E.c+(3/5)*E.s)^2≤61/100 := by
      nlinarith only [E.unit_normal,sq_nonneg ((3/5)*E.c-(1/2)*E.s)]
    nlinarith only [cauchy]
  apply le_of_not_gt
  intro below
  have lowerU : 3*E.c+(12/5)*E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply missingRight
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [low]
    · nlinarith only [corner.2.1,sign]
    · linarith only [below]
    · nlinarith only [corner.2.2.2,positive]
  have upperU : E.loU+E.side≤(7/2)*E.c+3*E.s := by
    apply le_of_not_gt
    intro high
    apply missingReach
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [outward.1,positive]
    · linarith only [high]
    · nlinarith only [below,canonical,positive]
    · nlinarith only [corner.2.2.2,sign]
  linarith only [lowerU,upperU,short,side]

/-- The whole E-transverse axis is unavailable. Both directions retain
strict original anchors, so tangencies do not create an omitted case. -/
theorem not_corner_transverse (E T : OpenSquare)
    (positive : 0<E.c) (sign : 0≤E.s) (side : 1<E.side)
    (corner : E.Inside 3 3) (topMarker : T.Inside 2 (1543/500))
    (topRow : T.Inside (12/5) 3)
    (floor : (12/5)*E.c-3*E.s≤E.loV)
    (separation : upper E (-E.s) E.c≤lower T (-E.s) E.c ∨
      upper T (-E.s) E.c≤lower E (-E.s) E.c) : False := by
  have normal : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
  rcases separation with below | above
  · have point := strict_bounds T _ _ (-E.s) E.c normal topRow
    rw [(ownV E).2] at below
    have short : (3/5)*(E.c+E.s)<1 := by
      have squared : (E.c+E.s)^2≤2 := by
        nlinarith only [E.unit_normal,sq_nonneg (E.c-E.s)]
      nlinarith only [squared]
    nlinarith only [below,point.1,floor,short,side]
  · have ep := strict_bounds E _ _ (-E.s) E.c normal corner
    have tp := strict_bounds T _ _ (-E.s) E.c normal topMarker
    nlinarith only [above,ep.1,tp.2,positive,sign]

/-- Under the negation of the desired corner reach, two positive
canonical frames have precisely these three directed SAT alternatives.
The right-wall foreign point is explicit and remains indispensable. -/
theorem alternatives (E T : OpenSquare)
    (ec : 0<E.c) (es : 0≤E.s) (en : E.s≤E.c)
    (tc : 0<T.c) (ts : 0≤T.s) (tn : T.s≤T.c)
    (same : E.side=T.side) (side : 1<E.side)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (missingReach : ¬E.Inside (7/2) 3)
    (topMarker : T.Inside 2 (1543/500)) (topRow : T.Inside (12/5) 3)
    (apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)) :
    upper T E.c E.s≤E.loU ∨
      T.loU+T.side≤lower E T.c T.s ∨
      upper E (-T.s) T.c≤T.loV := by
  have floor := lower_face E ec es en side corner outward missingRight missingReach
  have longitudinal (c s : ℝ) (positive : 0<c) (canonical : s≤c)
      (unit : c^2+s^2=1)
      (sep : upper E c s≤lower T c s ∨ upper T c s≤lower E c s) :
      upper T c s≤lower E c s := by
    rcases sep with reverse | forward
    · have ep := strict_bounds E _ _ c s unit corner
      have tp := strict_bounds T _ _ c s unit topMarker
      exfalso
      nlinarith only [reverse,ep.2,tp.1,positive,canonical]
    · exact forward
  have axes := CongruentSAT.faceSeparation_of_disjoint E T same apart
  change pairRadius E T≤|E.c*(centerX T-centerX E)+E.s*(centerY T-centerY E)| ∨
    pairRadius E T≤|-E.s*(centerX T-centerX E)+E.c*(centerY T-centerY E)| ∨
    pairRadius T E≤|T.c*(centerX T-centerX E)+T.s*(centerY T-centerY E)| ∨
    pairRadius T E≤|-T.s*(centerX T-centerX E)+T.c*(centerY T-centerY E)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius E nx ny+supportRadius T nx ny=R)
      (sep : R≤|nx*(centerX T-centerX E)+ny*(centerY T-centerY E)|) :=
    separated E T nx ny (by rwa [identity])
  rcases axes with eu | ev | tu | tv
  · left
    have h := longitudinal E.c E.s ec en E.unit_normal
      (separateAxis _ _ _ (parallel_radius E T) eu)
    simpa only [(ownU E).1] using h
  · exact False.elim (not_corner_transverse E T ec es side corner topMarker topRow floor
      (separateAxis _ _ _ (transverse_radius E T) ev))
  · right; left
    have identity : supportRadius E T.c T.s+supportRadius T T.c T.s=pairRadius T E := by
      rw [add_comm]; exact parallel_radius T E
    have h := longitudinal T.c T.s tc tn T.unit_normal
      (separateAxis _ _ _ identity tu)
    simpa only [(ownU T).2] using h
  · right; right
    have identity : supportRadius E (-T.s) T.c+supportRadius T (-T.s) T.c=pairRadius T E := by
      rw [add_comm]; exact transverse_radius T E
    rcases separateAxis _ _ _ identity tv with forward | reverse
    · simpa only [(ownV T).1] using forward
    · have normal : (-T.s)^2+T.c^2=1 := by nlinarith only [T.unit_normal]
      have ep := strict_bounds E _ _ (-T.s) T.c normal corner
      have tp := strict_bounds T _ _ (-T.s) T.c normal topMarker
      exfalso
      nlinarith only [reverse,ep.1,tp.2,tc,ts]

#print axioms lower_face
#print axioms not_corner_transverse
#print axioms alternatives
end N12Compact.UpperRightCornerReachAxes
