import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
An orbit normalization for the two opposite C696 owners.

The original half-turn exchanges owners 9 and 11 and sends height `y` to
`4 - y`. Normalize their *sum*, before any numerical propagation. This keeps
a coupled constraint absent from the old independent pose-domain state.
The theorem does not assert an exclusion of either remaining branch.
-/
namespace N12Compact.C696Symmetry

/-- The semantic facts required of a physical half-turn. There is no finite
certificate, source-state decoder or assumed center bound in this interface. -/
structure HeightSwap (Packing : Type) where
  valid : Packing → Prop
  bottom : Packing → ℝ
  top : Packing → ℝ
  turn : Packing → Packing
  preserves : ∀ p, valid p → valid (turn p)
  bottom_turn : ∀ p, valid p → bottom (turn p) = 4 - top p
  top_turn : ∀ p, valid p → top (turn p) = 4 - bottom p

/-- Choose one of the two physical representatives. Equality belongs to the
first branch, so the normalization loses no closed boundary configuration. -/
theorem joint_normal_form {Packing : Type} (s : HeightSwap Packing)
    (p : Packing) (hp : s.valid p) :
    ∃ q, (q = p ∨ q = s.turn p) ∧ s.valid q ∧
      s.bottom q + s.top q ≤ 4 := by
  by_cases h : s.bottom p + s.top p ≤ 4
  · exact ⟨p, Or.inl rfl, hp, h⟩
  · refine ⟨s.turn p, Or.inr rfl, s.preserves p hp, ?_⟩
    rw [s.bottom_turn p hp, s.top_turn p hp]
    linarith

/-- The useful middle-branch bound now follows before excluding the low
branch. The joint inequality can also be retained by a global linear proof. -/
theorem middle_top_bound (bottom top : ℝ)
    (joint : bottom + top ≤ 4) (high : 4 / 5 < bottom) :
    top < 16 / 5 := by
  linarith

/-- Only canonical packings need geometric exclusion, and both obligations
receive the extra joint inequality. The second receives its stronger top
bound without a recursive appeal to the first exclusion. -/
theorem exclusion_of_two_canonical_branches {Packing : Type}
    (s : HeightSwap Packing)
    (low : ∀ p, s.valid p → s.bottom p + s.top p ≤ 4 →
      s.bottom p ≤ 4 / 5 → False)
    (middle : ∀ p, s.valid p → s.bottom p + s.top p ≤ 4 →
      4 / 5 < s.bottom p → s.top p < 16 / 5 → False)
    (p : Packing) (hp : s.valid p) : False := by
  obtain ⟨q, _, hq, joint⟩ := joint_normal_form s p hp
  by_cases h : s.bottom q ≤ 4 / 5
  · exact low q hq joint h
  · have high : 4 / 5 < s.bottom q := lt_of_not_ge h
    exact middle q hq joint high
      (middle_top_bound (s.bottom q) (s.top q) joint high)

#print axioms joint_normal_form
#print axioms exclusion_of_two_canonical_branches

end N12Compact.C696Symmetry
