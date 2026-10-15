import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Elementary algebra for the exact C696 side-owner sign lemma.
The complete geometric derivation and integration map are in side-sign-proof.md.
These lemmas use no square-pose premise hidden in a coordinate bound.
-/

namespace C696SideSign

/-- The lower-right face cannot exclude D when the square lies right of the
left wall and its center height is at most two. -/
theorem positive_horizontal_strict (a u v : ℝ)
    (ha : 1 < a) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * u + (13 / 25 : ℝ) * v < a * (1 + u * u + u * v) := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hp : 0 < 1 + u * u + u * v := by
    nlinarith [sq_nonneg u]
  have hbound : 0 ≤ (1 - u)^2 + v * (u - (13 / 25 : ℝ)) := by
    by_cases hc : (13 / 25 : ℝ) ≤ u
    · have hprod : 0 ≤ v * (u - (13 / 25 : ℝ)) :=
        mul_nonneg hv (sub_nonneg.mpr hc)
      nlinarith [sq_nonneg (1 - u)]
    · have hc' : u < (13 / 25 : ℝ) := lt_of_not_ge hc
      have hprod : 0 ≤ (1 - v) * ((13 / 25 : ℝ) - u) :=
        mul_nonneg (sub_nonneg.mpr hv1) (sub_nonneg.mpr (le_of_lt hc'))
      nlinarith [sq_nonneg (u - (1 / 2 : ℝ))]
  have hstrict : 0 < (a - 1) * (1 + u * u + u * v) :=
    mul_pos (sub_pos.mpr ha) hp
  nlinarith

/-- The weighted projections on two adjacent lower faces cannot reach the
unit-side threshold when the square center height is at most two. -/
theorem adjacent_bound (u v : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (37 / 25 : ℝ) * u * v + (13 / 25 : ℝ) * v * v ≤ u + v := by
  have h1 : 0 ≤ u * (1 - v) := mul_nonneg hu (sub_nonneg.mpr hv1)
  have h2a : 0 ≤ (12 / 25 : ℝ) * (1 - u) + (13 / 25 : ℝ) * (1 - v) := by
    nlinarith
  have h2 : 0 ≤ v * ((12 / 25 : ℝ) * (1 - u) + (13 / 25 : ℝ) * (1 - v)) :=
    mul_nonneg hv h2a
  nlinarith

theorem adjacent_strict_of_sum_pos (a u v : ℝ)
    (ha : 1 < a) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hpos : 0 < u + v) :
    (37 / 25 : ℝ) * u * v + (13 / 25 : ℝ) * v * v < a * (u + v) := by
  have hbound := adjacent_bound u v hu hu1 hv hv1
  have hstrict : 0 < (a - 1) * (u + v) := mul_pos (sub_pos.mpr ha) hpos
  nlinarith

theorem adjacent_strict (a u v : ℝ)
    (ha : 1 < a) (hu : 0 < u) (hu1 : u ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1) :
    (37 / 25 : ℝ) * u * v + (13 / 25 : ℝ) * v * v < a * (u + v) := by
  have hbound := adjacent_bound u v (le_of_lt hu) hu1 (le_of_lt hv) hv1
  have hstrict : 0 < (a - 1) * (u + v) :=
    mul_pos (sub_pos.mpr ha) (add_pos hu hv)
  nlinarith

#print axioms positive_horizontal_strict
#print axioms adjacent_bound
#print axioms adjacent_strict

end C696SideSign
