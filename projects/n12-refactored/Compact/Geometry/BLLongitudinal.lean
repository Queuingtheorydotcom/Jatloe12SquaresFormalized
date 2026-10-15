import Compact.Geometry.BLSeparation

/-!
Two of the template's original missing points eliminate L's remaining
transverse separator. Together with BLSeparation, only the two forward
longitudinal separating axes remain. No angle discretization is used.
-/

namespace N12Compact.BLLongitudinal

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare C977ChainBridge

/-- A signed canonical L cannot put its upper transverse face below B's
bottom compulsory point while satisfying its own required/missing points.
The two final numerical contradictions are widths strictly below one. -/
theorem no_negative_transverse_cap (L : OpenSquare)
    (lc : 0 < L.c) (ls : L.s ≤ 0) (lsc : |L.s| ≤ L.c)
    (ha : 1 < L.side)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5))
    (mw : ¬ L.Inside (19 / 25) (187 / 100))
    (mp : ¬ L.Inside (33 / 20) (33 / 20))
    (cap : L.loV + L.side ≤ -L.s * (33 / 20) + L.c * (47 / 20)) : False := by
  have hunit := L.unit_normal
  have hcs : 0 ≤ L.c + L.s := by
    have hh := (abs_le.mp lsc).1
    linarith only [hh]
  have hc1 : L.c ≤ 1 := by nlinarith only [hunit, sq_nonneg L.s]
  have hsum : L.c - L.s ≤ 10 / 7 := by
    nlinarith only [hunit, sq_nonneg (L.c + L.s), lc, ls]
  have wu : L.c * (19 / 25) + L.s * (187 / 100) < L.loU + L.side := by
    have hh := ll.2.1
    nlinarith only [hh, lc, hcs]
  have wv : -L.s * (19 / 25) + L.c * (187 / 100) < L.loV + L.side := by
    have hh := lt.2.2.2
    nlinarith only [hh, lc, ls]
  have wbelow : L.c * (19 / 25) + L.s * (187 / 100) ≤ L.loU ∨
      -L.s * (19 / 25) + L.c * (187 / 100) ≤ L.loV := by
    by_cases hu : L.c * (19 / 25) + L.s * (187 / 100) ≤ L.loU
    · exact Or.inl hu
    · right
      by_contra hv
      exact mw ⟨lt_of_not_ge hu, wu, lt_of_not_ge hv, wv⟩
  rcases wbelow with hu | hv
  · have ratio : 0 ≤ 24 * L.c + 53 * L.s := by
      have hh := lt.1
      nlinarith only [hu, hh]
    have pu : L.loU < L.c * (33 / 20) + L.s * (33 / 20) := by
      have hh := lt.1
      nlinarith only [hh, lc, ls]
    have pv : -L.s * (33 / 20) + L.c * (33 / 20) < L.loV + L.side := by
      have hh := ll.2.2.2
      nlinarith only [hh, ratio, lc]
    have pabove : L.loU + L.side ≤ L.c * (33 / 20) + L.s * (33 / 20) := by
      by_contra hh
      have pl : L.loV < -L.s * (33 / 20) + L.c * (33 / 20) := by
        nlinarith only [cap, hc1, ha]
      exact mp ⟨pu, lt_of_not_ge hh, pl, pv⟩
    have hwidth : 100 < 89 * L.c - 22 * L.s := by
      nlinarith only [hu, pabove, ha]
    have hsmall : (89 * L.c - 22 * L.s) ^ 2 ≤ 8405 := by
      nlinarith only [hunit, sq_nonneg (22 * L.c + 89 * L.s)]
    nlinarith only [hwidth, hsmall]
  · have hwidth : L.side ≤ (12 / 25) * L.c - (89 / 100) * L.s := by
      nlinarith only [hv, cap]
    nlinarith only [hwidth, hcs, hsum, ha]

/-- In the original four-square template, B and L must separate on one
of their forward longitudinal axes. All transverse alternatives are
excluded from actual point membership and the two original missing points. -/
theorem two_directed_alternatives (B L : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < L.side)
    (bb : ClosedInside B (33 / 20) (47 / 20))
    (bt : ClosedInside B (8 / 5) 3)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5))
    (mw : ¬ L.Inside (19 / 25) (187 / 100))
    (mp : ¬ L.Inside (33 / 20) (33 / 20))
    (same : B.side = L.side)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) :
    pairRadius B L ≤
        B.c * (centerX B - centerX L) + B.s * (centerY B - centerY L) ∨
    pairRadius L B ≤
        L.c * (centerX B - centerX L) + L.s * (centerY B - centerY L) := by
  rcases BLSeparation.three_directed_alternatives B L bc bs bsc lc lsc bb bt ll lt
    same apart with hu | hu | hv
  · exact Or.inl hu
  · exact Or.inr hu
  · have ls : L.s ≤ 0 := by nlinarith only [hv.1, lc]
    have radius : pairRadius L B = L.side / 2 + supportRadius B (-L.s) L.c := by
      have hc : -L.s * B.c + L.c * B.s = normalCross L B := by
        unfold normalCross
        ring
      have hd : -(-L.s) * B.s + L.c * B.c = normalDot L B := by
        unfold normalDot
        ring
      simp only [pairRadius, supportRadius, hc, hd]
      ring
    have point := (abs_le.mp (closed_support B (33 / 20) (47 / 20)
      (-L.s) L.c bb)).1
    have center := (center_coordinates L).2
    have cap : L.loV + L.side ≤ -L.s * (33 / 20) + L.c * (47 / 20) := by
      nlinarith only [point, center, radius, hv.2]
    exact False.elim (no_negative_transverse_cap L lc ls lsc ha ll lt mw mp cap)

end N12Compact.BLLongitudinal
