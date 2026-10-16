import Compact.Geometry.ClosedFrames

/-! Exact face reductions for a square owning both left central markers.
These retain center escape as a hypothesis. They do not assert that a
neighboring wall, or the auxiliary budget alone, rules out that escape. -/
namespace N12Compact.MergedLeftEscape
open S12 S12Pilot
set_option Elab.async false

theorem center_cap (A : OpenSquare) (hc : 0 < A.c)
    (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (missing : ¬ A.Inside 2 2) : A.loU+A.side ≤ 2*(A.c+A.s) := by
  apply le_of_not_gt
  intro upper
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [bottom.1,hc,hs]
  · linarith only [upper]
  · linarith only [bottom.2.2.1,order]
  · linarith only [top.2.2.2,hc,hs]

/-- The actual left wall owns this auxiliary point in the intended
applications. Its exclusion selects the upper transverse face of A. -/
theorem upper_v (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (cap : A.loU+A.side ≤ 2*(A.c+A.s))
    (missing : ¬ A.Inside 1 (113/50)) :
    A.loV+A.side ≤ (113/50)*A.c-A.s := by
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  apply le_of_not_gt
  intro upper
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,cu,hs]
  · linarith only [top.2.1,hc,hs]
  · linarith only [bottom.2.2.1,hc,hs]
  · linarith only [upper]

/-- The lower left auxiliary point can escape through just these two
faces; no sign choice for the neighboring square is assumed. -/
theorem left_aux_faces (A : OpenSquare) (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (missing : ¬ A.Inside 1 (87/50)) :
    A.c+(87/50)*A.s ≤ A.loU ∨ A.loV+A.side ≤ (87/50)*A.c-A.s := by
  by_cases lower : A.c+(87/50)*A.s ≤ A.loU
  · exact Or.inl lower
  · right
    apply le_of_not_gt
    intro upper
    apply missing
    refine ⟨by linarith only [lt_of_not_ge lower],?_,?_,?_⟩
    · linarith only [top.2.1,hc,hs]
    · linarith only [bottom.2.2.1,hc,hs]
    · linarith only [upper]

/-- At the lower inward point the complementary two faces are the only
possibilities. This is useful together with the real one-point F budget. -/
theorem inward_aux_faces (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (top : A.Inside (33/20) (47/20))
    (cap : A.loU+A.side ≤ 2*(A.c+A.s))
    (missing : ¬ A.Inside 2 (87/50)) :
    A.loU+A.side ≤ 2*A.c+(87/50)*A.s ∨
      (87/50)*A.c-2*A.s ≤ A.loV := by
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  by_cases upper : A.loU+A.side ≤ 2*A.c+(87/50)*A.s
  · exact Or.inl upper
  · right
    apply le_of_not_gt
    intro lower
    apply missing
    refine ⟨?_,by linarith only [lt_of_not_ge upper],?_,?_⟩
    · linarith only [cap,side,order,cu]
    · linarith only [lower]
    · linarith only [top.2.2.2,hc,hs]

#print axioms center_cap
#print axioms upper_v
end N12Compact.MergedLeftEscape
