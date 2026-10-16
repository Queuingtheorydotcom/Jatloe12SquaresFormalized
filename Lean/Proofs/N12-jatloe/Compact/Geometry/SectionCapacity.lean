import S12.WallGeometry
import S12.Container
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
Long sections need no sorting or endpoint-order enumeration. Every interval
longer than one in [0,4] contains one of 1,2,3 strictly. Distinct squares in
an actual packing cannot use the same point. With m cuts there are 3m slots.

This proves the geometric capacity step in the 59-case simplification.
The long-section premises still require the case enclosure certificates.
-/
namespace N12Compact.SectionCapacity
open S12 S12Pilot

theorem interval_hits (l u : ℝ) (hl : 0 ≤ l) (hu : u ≤ 4)
    (hw : 1 < u - l) :
    ∃ j : Fin 3, l < (j.val : ℝ) + 1 ∧ (j.val : ℝ) + 1 < u := by
  by_cases h1 : l < 1
  · refine ⟨0, ?_, ?_⟩ <;> norm_num <;> linarith
  by_cases h2 : l < 2
  · refine ⟨1, ?_, ?_⟩ <;> norm_num <;> linarith
  by_cases h3 : l < 3
  · refine ⟨2, ?_, ?_⟩ <;> norm_num <;> linarith
  · exfalso
    linarith

/-- A genuine open horizontal segment in the original square, longer than
one. The endpoints may lie on the square boundary. -/
def LongSection (q : OpenSquare) (h : ℝ) : Prop :=
  ∃ l u : ℝ, 1 < u - l ∧ ∀ x, l < x → x < u → q.Inside x h

theorem section_hits (q : OpenSquare) (h : ℝ)
    (hbox : InsideContainer q) (hsection : LongSection q h) :
    ∃ j : Fin 3, q.Inside ((j.val : ℝ) + 1) h := by
  obtain ⟨l, u, hw, hs⟩ := hsection
  have hl : 0 ≤ l := by
    apply affine_endpoint_nonnegative (u - l) 1 l (by linarith)
    intro t ht0 ht1
    have hp := (hbox (l + t) h (hs _ (by linarith) (by linarith))).1
    linarith only [hp]
  have hu : u ≤ 4 := by
    have bound : 0 ≤ 4 - u := by
      apply affine_endpoint_nonnegative (u - l) 1 (4 - u) (by linarith)
      intro t ht0 ht1
      have hp := (hbox (u - t) h (hs _ (by linarith) (by linarith))).2.1
      linarith only [hp]
    linarith only [bound]
  obtain ⟨j, hjl, hju⟩ := interval_hits l u hl hu hw
  exact ⟨j, hs _ hjl hju⟩

/-- No choice enumeration: choose any one cut met by each square, then any
one strict grid point in its section. Interior disjointness makes the resulting
map into Fin m × Fin 3 injective. This includes all endpoint equalities. -/
theorem multi_cut_capacity {n m : ℕ} (q : Fin n → OpenSquare) (cuts : Fin m → ℝ)
    (hbox : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hsections : ∀ i, ∃ k, LongSection (q i) (cuts k)) : n ≤ m * 3 := by
  classical
  have hits : ∀ i, ∃ p : Fin m × Fin 3,
      (q i).Inside ((p.2.val : ℝ) + 1) (cuts p.1) := by
    intro i
    obtain ⟨k, hk⟩ := hsections i
    obtain ⟨j, hj⟩ := section_hits (q i) (cuts k) (hbox i) hk
    exact ⟨(k,j), hj⟩
  choose point inside using hits
  have injective : Function.Injective point := by
    intro i j he
    by_contra hij
    have hi := inside i
    rw [he] at hi
    exact hd i j hij _ _ ⟨hi, inside j⟩
  have bound := Fintype.card_le_of_injective point injective
  simpa only [Fintype.card_prod, Fintype.card_fin] using bound

theorem four_on_one_cut (q : Fin 4 → OpenSquare) (h : ℝ)
    (hbox : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hsections : ∀ i, LongSection (q i) h) : False := by
  have bound := multi_cut_capacity q (fun _ : Fin 1 => h) hbox hd
    (fun i => ⟨0, hsections i⟩)
  norm_num at bound

theorem seven_on_two_cuts (q : Fin 7 → OpenSquare) (h₀ h₁ : ℝ)
    (hbox : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hsections : ∀ i, LongSection (q i) h₀ ∨ LongSection (q i) h₁) : False := by
  let cuts : Fin 2 → ℝ := fun k => if k = 0 then h₀ else h₁
  have hits : ∀ i, ∃ k, LongSection (q i) (cuts k) := by
    intro i
    rcases hsections i with h | h
    · exact ⟨0, by simpa [cuts] using h⟩
    · exact ⟨1, by simpa [cuts] using h⟩
  have bound := multi_cut_capacity q cuts hbox hd hits
  norm_num at bound

#print axioms multi_cut_capacity
#print axioms seven_on_two_cuts
end N12Compact.SectionCapacity
