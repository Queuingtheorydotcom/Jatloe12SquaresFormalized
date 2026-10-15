import Compact.Bridge.CongruentSAT

/-!
The wall-chain cut for disjoint original squares with equal side lengths.

This adapter discharges the exact separating-axis premise of C977ChainBridge
using CongruentSAT. It preserves the original open-square model, including
legal boundary contact. Near-axis, height-band and gap bounds remain explicit
geometric inputs: their case-specific coverage is not asserted here.

The separate adapter avoids a dependency cycle: CongruentSAT uses the shared
FaceSeparation definition from C977ChainBridge.
-/

namespace N12Compact.C977ChainBridge

open S12 S12Pilot S12Completion.C977

/-- Equal-side disjointness supplies the exact four-axis separation premise. -/
theorem face_separation_of_disjoint (q r : OpenSquare)
    (hside : q.side = r.side)
    (hd : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y)) :
    FaceSeparation q r :=
  CongruentSAT.faceSeparation_of_disjoint q r hside hd

/-- The adjacent-pair support gain follows from actual open-square
disjointness; no separating-axis premise is left to the caller. -/
theorem pair_step_of_disjoint (q r : OpenSquare) (a h : ℝ)
    (ha : 1 < a) (hqa : q.side = a) (hra : r.side = a)
    (hq : NearAxis q) (hr : NearAxis r)
    (hX : 0 ≤ centerX r - centerX q)
    (hY : |centerY r - centerY q| ≤ h)
    (hforward : 0 < (99 / 100) * (centerX r - centerX q) - (1 / 10) * h)
    (htransverse : (1 / 10) * (centerX r - centerX q) + h < 1)
    (hd : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y)) :
    ∃ b : ℝ, (b = q.s ∨ b = r.s) ∧
      a + a * (43 / 100) * |r.s - q.s| - b * (centerY r - centerY q) ≤
        centerX r - centerX q :=
  pair_step_of_face_separation q r a h ha hqa hra hq hr hX hY
    hforward htransverse
    (face_separation_of_disjoint q r (hqa.trans hra.symm) hd)

/-- A chain bound from adjacent disjointness in the original square model.
The terminal wall condition is actual containment in the original box. -/
theorem openSquare_chain_cut_of_disjoint
    (n : ℕ) (q : ℕ → OpenSquare) (a lower h : ℝ)
    (ha : 1 < a) (hh : h ≤ 43 / 100)
    (hside : ∀ i, i ≤ n → (q i).side = a)
    (hnormal : ∀ i, i ≤ n → NearAxis (q i))
    (hheight : ∀ i, i ≤ n → lower ≤ centerY (q i) ∧ centerY (q i) ≤ lower + h)
    (hgap : ∀ i, i < n →
      0 ≤ centerX (q (i + 1)) - centerX (q i) ∧
      0 < (99 / 100) * (centerX (q (i + 1)) - centerX (q i)) - (1 / 10) * h ∧
      (1 / 10) * (centerX (q (i + 1)) - centerX (q i)) + h < 1)
    (hdisjoint : ∀ i, i < n → ∀ x y,
      ¬ ((q i).Inside x y ∧ (q (i + 1)).Inside x y))
    (hwall : ∀ x y, (q n).Inside x y → 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4) :
    centerX (q 0) < 4 - ((n : ℝ) + 1 / 2) := by
  apply openSquare_chain_cut n q a lower h ha hh hside hnormal hheight hgap ?_ hwall
  intro i hi
  have hi0 : i ≤ n := Nat.le_of_lt hi
  have hi1 : i + 1 ≤ n := hi
  exact face_separation_of_disjoint (q i) (q (i + 1))
    ((hside i hi0).trans (hside (i + 1) hi1).symm) (hdisjoint i hi)

end N12Compact.C977ChainBridge
