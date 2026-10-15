import Compact.Geometry.ClosedPointExclusion

/-! A continuous angle exclusion from four actual owned points.

In Case713, Q is original owner7 (mask2304) in the branch owning F5,
and A is original owner6 (mask512). The two Q points must be strict;
the two foreign A points may be closed. No enclosure, angle grid,
side bound, or assumed packing exclusion is used.
-/

namespace N12Compact.CentralSegmentAngle

open S12 S12Pilot FourSquareAnchors

/-- A shallow nonnegative frame forces Q to meet the foreign segment.
The intersection point is selected symbolically from the frame ratio. -/
theorem exclude_small_nonnegative (Q A : OpenSquare)
    (hc : 0 < Q.c) (hs : 0 ≤ Q.s) (hsmall : Q.s ≤ Q.c / 2)
    (p : Q.Inside (33/20) (33/20))
    (d : Q.Inside 2 (113/50))
    (e : ClosedInside A 2 (87/50))
    (m : ClosedInside A (113/50) 2)
    (apart : ∀ x y, ¬ (Q.Inside x y ∧ A.Inside x y)) : False := by
  let r : ℝ := Q.s / Q.c
  have hr0 : 0 ≤ r := div_nonneg hs hc.le
  have hr2 : r ≤ 1/2 := by
    apply (div_le_iff₀ hc).mpr
    linarith only [hsmall]
  have hrc : r * Q.c = Q.s := div_mul_cancel₀ Q.s (ne_of_gt hc)
  let t : ℝ := 17*r/50
  have ht0 : 0 ≤ t := by
    exact div_nonneg (mul_nonneg (by norm_num) hr0) (by norm_num)
  have htcap : t ≤ 17/100 := by dsimp [t]; linarith only [hr2]
  let X : ℝ := 2+t
  let Y : ℝ := 87/50+t

  have ulo : Q.c*(33/20)+Q.s*(33/20) ≤ Q.c*X+Q.s*Y := by
    dsimp only [X,Y]
    nlinarith only [hc, hs, mul_nonneg hc.le ht0, mul_nonneg hs ht0]
  have ucoef : 0 ≤ r*(9-17*r)/50 := by
    have hn : 0 ≤ 9-17*r := by linarith only [hr2]
    exact div_nonneg (mul_nonneg hr0 hn) (by norm_num)
  have uhi : Q.c*X+Q.s*Y ≤ Q.c*2+Q.s*(113/50) := by
    have hprod := mul_nonneg hc.le ucoef
    rw [← hrc]
    dsimp only [X,Y,t]
    nlinarith only [hprod]
  have vcoef : 0 ≤ (9-r-34*r^2)/100 := by
    have factors := mul_nonneg
      (show 0 ≤ 1-2*r by linarith only [hr2])
      (show 0 ≤ 9+17*r by linarith only [hr0])
    nlinarith only [factors]
  have vlo : -Q.s*(33/20)+Q.c*(33/20) ≤ -Q.s*X+Q.c*Y := by
    have hprod := mul_nonneg hc.le vcoef
    rw [← hrc]
    dsimp only [X,Y,t]
    nlinarith only [hprod]
  have vhi : -Q.s*X+Q.c*Y ≤ -Q.s*2+Q.c*(113/50) := by
    have positive := mul_pos hc
      (show 0 < 13/25-t by linarith only [htcap])
    have nonnegative := mul_nonneg ht0 hs
    dsimp only [X,Y]
    nlinarith only [positive, nonnegative]
  have inside : Q.Inside X Y :=
    ⟨p.1.trans_le ulo, uhi.trans_lt d.2.1,
      p.2.2.1.trans_le vlo, vhi.trans_lt d.2.2.2⟩

  let weight : ℝ := 17*r/13
  have hw0 : 0 ≤ weight := by
    exact div_nonneg (mul_nonneg (by norm_num) hr0) (by norm_num)
  have hw1 : weight ≤ 1 := by dsimp [weight]; linarith only [hr2]
  have foreign := ClosedPointExclusion.closed_segment A
    2 (87/50) (113/50) 2 weight e m hw0 hw1
  have hx : (1-weight)*2+weight*(113/50) = X := by
    dsimp [weight,X,t]
    ring
  have hy : (1-weight)*(87/50)+weight*2 = Y := by
    dsimp [weight,Y,t]
    ring
  rw [hx,hy] at foreign
  exact ClosedPointExclusion.outside_of_closed Q A X Y apart foreign inside

/-- The excluded interval is continuous and includes both endpoints.
This is an orientation restriction, not an entire Case713 exclusion. -/
theorem angle_gap (Q A : OpenSquare) (hc : 0 < Q.c)
    (p : Q.Inside (33/20) (33/20))
    (d : Q.Inside 2 (113/50))
    (e : ClosedInside A 2 (87/50))
    (m : ClosedInside A (113/50) 2)
    (apart : ∀ x y, ¬ (Q.Inside x y ∧ A.Inside x y)) :
    Q.s < 0 ∨ Q.c/2 < Q.s := by
  by_cases hs : 0 ≤ Q.s
  · right
    apply lt_of_not_ge
    intro hsmall
    exact exclude_small_nonnegative Q A hc hs hsmall p d e m apart
  · exact Or.inl (lt_of_not_ge hs)

#print axioms exclude_small_nonnegative
#print axioms angle_gap
end N12Compact.CentralSegmentAngle
