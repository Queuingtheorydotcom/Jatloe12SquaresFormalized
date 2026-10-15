import S12.Convex

/-! Exact upper-face consequences in the still-open positive central sector.
These lemmas do not assert the desired left point or a whole corner theorem.
The upper northwest face follows from the two strict crosspoints and the
actual foreign left-singleton point (1,1.6), independent of a center escape.
-/
namespace N12Compact.PositiveCentralLeftBand

open S12 S12Pilot
set_option Elab.async false

/-- Three bands at (1,2) follow from the original points and the upper-U
center escape. Failure to own (1,2) therefore has exactly this upper-V form. -/
theorem upper_face (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (cap : A.loU+A.side ≤ 2*(A.c+A.s))
    (marker : A.Inside (33/20) (33/20))
    (west : A.Inside (3/2) 2) (missing : ¬A.Inside 1 2) :
    A.loV+A.side ≤ 2*A.c-A.s := by
  have cBound : A.c ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg A.s,sq_nonneg (A.c-1)]
  apply le_of_not_gt
  intro upper
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,cBound]
  · linarith only [west.2.1,hc]
  · linarith only [marker.2.2.1,hc,hs]
  · linarith only [upper]

/-- Absence of the northwest central marker and the actual left singleton's
point (1,1.6) give an upper-V cap from the two genuine strict crosspoints.
Otherwise the U-width would be at most .65*c+.75*s, whose norm is below 1. -/
theorem northwest_cap (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (west : A.Inside (3/2) 2) (below : A.Inside 2 (3/2))
    (missingNW : ¬A.Inside (33/20) (47/20))
    (foreignLow : ¬A.Inside 1 (8/5)) :
    A.loV+A.side ≤ (47/20)*A.c-(33/20)*A.s := by
  by_contra failure
  have upper : (47/20)*A.c-(33/20)*A.s < A.loV+A.side := lt_of_not_ge failure
  have northwestU : A.loU+A.side ≤ (33/20)*A.c+(47/20)*A.s := by
    apply le_of_not_gt
    intro high
    apply missingNW
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [west.1,hc,hs]
    · linarith only [high]
    · linarith only [west.2.2.1,hc,order]
    · linarith only [upper]
  have leftU : A.c+(8/5)*A.s ≤ A.loU := by
    apply le_of_not_gt
    intro lower
    apply foreignLow
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [lower]
    · linarith only [west.2.1,hc,hs]
    · linarith only [below.2.2.1,hc,hs]
    · linarith only [upper,hc,order]
  have short : (13/20)*A.c+(3/4)*A.s < 1 := by
    nlinarith only [A.unit_normal,
      sq_nonneg (A.c-13/20),sq_nonneg (A.s-3/4)]
  linarith only [northwestU,leftU,short,side]

/-- The desired left point, if obtained from the actual neighboring squares,
would immediately restrict the remaining central angle. -/
theorem left_point_tilt (A : OpenSquare)
    (cap : A.loV+A.side ≤ (47/20)*A.c-(33/20)*A.s)
    (point : A.Inside 1 2) : 13*A.s < 7*A.c := by
  linarith only [cap,point.2.2.2]

end N12Compact.PositiveCentralLeftBand
