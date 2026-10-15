import Compact.Core.CachedSupportFan

/-! Numeric fan replay without proof-bearing dictionary parameters.

The numeric checker sees only references, integer bases and lookup hints. A
separate generic theorem connects those values to actual input-row proofs.
Every selected basis must still pass its cone and strict pair inequality on
each of the eight actual axes. Neither sortedness nor complete fan coverage
is assumed by the soundness theorem.
-/

set_option Elab.async false

namespace N12Compact.RawSupportFan
open IntegerSupport ReferenceAxis PairPruning

structure Entry where
  start : Nat
  basis : VertexSupport.Basis

structure Context where
  reference : Reference
  fallback : Entry
  entries : Array Entry

def search (entries : Array Entry) (key : Nat) : Nat → Nat → Nat → Entry → Entry
  | 0, _, _, best => best
  | fuel + 1, lo, hi, best =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match entries[mid]? with
        | none => best
        | some entry =>
            if entry.start ≤ key then search entries key fuel (mid + 1) hi entry
            else search entries key fuel lo mid best
      else best

def Context.select (context : Context) (key : Nat) : Entry :=
  search context.entries key 16 0 context.entries.size context.fallback

/-- Semantic evidence, kept out of every numeric checker type. -/
def Entry.ValidFor (entry : Entry) (holds : (Fin 2 → ℝ) → Prop) : Prop :=
  entry.basis.Check ∧
  ∀ p, holds p → entry.basis.first.Holds p ∧ entry.basis.second.Holds p

def Context.ValidFor (context : Context) (holds : (Fin 2 → ℝ) → Prop) : Prop :=
  context.fallback.ValidFor holds ∧
  ∀ (i : Nat) (entry : Entry), context.entries[i]? = some entry → entry.ValidFor holds

theorem search_valid (entries : Array Entry) (key : Nat)
    (holds : (Fin 2 → ℝ) → Prop)
    (valid : ∀ (i : Nat) (entry : Entry), entries[i]? = some entry → entry.ValidFor holds)
    (fuel lo hi : Nat) (best : Entry) (hbest : best.ValidFor holds) :
    (search entries key fuel lo hi best).ValidFor holds := by
  induction fuel generalizing lo hi best with
  | zero => exact hbest
  | succ fuel ih =>
      simp only [search]
      split
      · split
        · exact hbest
        · rename_i entry he
          split
          · exact ih _ _ _ (valid _ _ he)
          · exact ih _ _ _ hbest
      · exact hbest

theorem Context.select_valid (context : Context) (holds : (Fin 2 → ℝ) → Prop)
    (valid : context.ValidFor holds) (key : Nat) :
    (context.select key).ValidFor holds :=
  search_valid context.entries key holds valid.2 _ _ _ _ valid.1

def PairCheck (a b : Context) (keys : Fin 8 → Nat) (opposite : Nat → Nat) : Prop :=
  ∀ i : Fin 8,
    let n := direction a.reference b.reference i
    let A := (a.select (keys i)).basis
    let B := (b.select (opposite (keys i))).basis
    A.Cone n.x n.y ∧ B.Cone (-n.x) (-n.y) ∧
      VertexSupport.PairCheck A B n.x n.y (CachedSupportFan.scale a.reference b.reference)
        (target a.reference b.reference n).constant

instance (a b : Context) (keys : Fin 8 → Nat) (opposite : Nat → Nat) :
    Decidable (PairCheck a b keys opposite) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, _ ∧ _))

theorem pair_sound (a b : Context) (P Q : (Fin 2 → ℝ) → Prop)
    (av : a.ValidFor P) (bv : b.ValidFor Q)
    (ha : a.reference.Valid) (hb : b.reference.Valid)
    (hac : a.reference.value.Check) (hbc : b.reference.value.Check)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : PairCheck a b keys opposite) (p q : Fin 2 → ℝ)
    (hp : P p) (hq : Q q) :
    S12.OverlapsAt (a.reference.value.toSquare hac) (b.reference.value.toSquare hbc)
      (p 0, p 1) (q 0, q 1) := by
  apply ReferenceAxis.overlap a.reference b.reference ha hb hac hbc p q
  intro n hn
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hn
  let j : Fin 8 := ⟨i.val, by simpa [directions] using i.isLt⟩
  have he : direction a.reference b.reference j = n := by
    simpa [direction, j] using hi
  rw [← he, CachedSupportFan.target_factor]
  obtain ⟨coneA, coneB, bound⟩ := checked j
  have A := a.select_valid P av (keys j)
  have B := b.select_valid Q bv (opposite (keys j))
  apply VertexSupport.pair_sound _ _ A.1 B.1 _ _ _ _
    (CachedSupportFan.scale_positive _ _ ha hb) bound p q
  · exact VertexSupport.Basis.sound _ A.1 _ _ coneA p (A.2 p hp).1 (A.2 p hp).2
  · exact VertexSupport.Basis.sound _ B.1 _ _ coneB q (B.2 q hq).1 (B.2 q hq).2

end N12Compact.RawSupportFan

namespace N12Compact.CachedSupportFan
open IntegerSupport

def Entry.numeric {r : Nat} (entry : Entry r) : RawSupportFan.Entry :=
  ⟨entry.start, entry.basis⟩

def Context.numeric {r : Nat} {rows : Fin r → Row} (context : Context rows) :
    RawSupportFan.Context :=
  ⟨context.reference, context.fallback.val.numeric,
    context.entries.map (fun entry => entry.val.numeric)⟩

theorem Certified.numeric_valid {r : Nat} {rows : Fin r → Row}
    {inputs : List (Fin r)} (entry : Certified rows inputs) :
    entry.val.numeric.ValidFor (fun p => ∀ i ∈ inputs, (rows i).Holds p) := by
  obtain ⟨first, second, first_eq, second_eq, vertex⟩ := entry.property
  refine ⟨vertex, ?_⟩
  intro p holds
  change entry.val.basis.first.Holds p ∧ entry.val.basis.second.Holds p
  rw [first_eq, second_eq]
  exact ⟨holds _ first, holds _ second⟩

/-- Prove this once per context. Numeric checks can then use a materialized
`RawSupportFan.Context` linked by an ordinary equality, with no dictionary in
the checker's type or arithmetic expressions. -/
theorem Context.numeric_valid {r : Nat} {rows : Fin r → Row}
    (context : Context rows) :
    context.numeric.ValidFor (fun p => ∀ i ∈ context.inputs, (rows i).Holds p) := by
  refine ⟨context.fallback.numeric_valid, ?_⟩
  intro i entry he
  change (context.entries.map (fun e => e.val.numeric))[i]? = some entry at he
  rw [Array.getElem?_map] at he
  cases hlookup : context.entries[i]? with
  | none => simp [hlookup] at he
  | some original =>
      have equal : original.val.numeric = entry := by simpa [hlookup] using he
      rw [← equal]
      exact original.numeric_valid

theorem Context.cached_numeric_valid {r : Nat} {rows : Fin r → Row}
    (context : Context rows) (cached : RawSupportFan.Context)
    (equal : cached = context.numeric) :
    cached.ValidFor (fun p => ∀ i ∈ context.inputs, (rows i).Holds p) := by
  rw [equal]
  exact context.numeric_valid

end N12Compact.CachedSupportFan

#print axioms N12Compact.RawSupportFan.pair_sound
#print axioms N12Compact.CachedSupportFan.Context.cached_numeric_valid
