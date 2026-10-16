import Compact.Core.VertexSupport
import Compact.Core.PairPruning

/-!
Input membership, copied row values and a basis vertex are certified once per
fan entry. Numeric pair checks use only those small cached values, cone signs
and the final scalar bound. They never unfold the global row dictionary.
-/

set_option Elab.async false

namespace N12Compact.CachedSupportFan

open IntegerSupport ReferenceAxis PairPruning

structure Entry (r : Nat) where
  start : Nat
  first : Fin r
  second : Fin r
  basis : VertexSupport.Basis

def Entry.Check {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r))
    (entry : Entry r) : Prop :=
  entry.first ∈ inputs ∧ entry.second ∈ inputs ∧
  entry.basis.first = rows entry.first ∧ entry.basis.second = rows entry.second ∧
  entry.basis.Check

instance {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r)) (entry : Entry r) :
    Decidable (entry.Check rows inputs) := inferInstanceAs (Decidable (_ ∧ _))

abbrev Certified {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r)) :=
  {entry : Entry r // entry.Check rows inputs}

def search {r : Nat} {rows : Fin r → Row} {inputs : List (Fin r)}
    (entries : Array (Certified rows inputs)) (key : Nat) :
    Nat → Nat → Nat → Certified rows inputs → Certified rows inputs
  | 0, _, _, best => best
  | fuel+1, lo, hi, best =>
      if lo < hi then
        let mid := (lo+hi)/2
        match entries[mid]? with
        | none => best
        | some entry =>
            if entry.val.start ≤ key then
              search entries key fuel (mid+1) hi entry
            else search entries key fuel lo mid best
      else best

structure Context {r : Nat} (rows : Fin r → Row) where
  inputs : List (Fin r)
  reference : Reference
  fallback : Certified rows inputs
  entries : Array (Certified rows inputs)

def Context.select {r : Nat} {rows : Fin r → Row} (context : Context rows)
    (key : Nat) : Certified rows context.inputs :=
  search context.entries key 16 0 context.entries.size context.fallback

theorem Certified.support {r : Nat} {rows : Fin r → Row} {inputs : List (Fin r)}
    (entry : Certified rows inputs) (x y : Int) (cone : entry.val.basis.Cone x y)
    (p : Fin 2 → ℝ) (holds : ∀ i ∈ inputs, (rows i).Holds p) :
    (entry.val.basis.bound x y).Holds p := by
  obtain ⟨first,second,first_eq,second_eq,vertex⟩ := entry.property
  apply entry.val.basis.sound vertex x y cone p
  · rw [first_eq]; exact holds _ first
  · rw [second_eq]; exact holds _ second

def scale (a b : Reference) : Int :=
  2 * a.denominator * a.sideDenominator * b.denominator * b.sideDenominator

theorem scale_positive (a b : Reference) (ha : a.Valid) (hb : b.Valid) :
    0 < scale a b := by
  have ha₁ : (0 : Int) < a.denominator := by exact_mod_cast ha.1
  have ha₂ : (0 : Int) < a.sideDenominator := by exact_mod_cast ha.2
  have hb₁ : (0 : Int) < b.denominator := by exact_mod_cast hb.1
  have hb₂ : (0 : Int) < b.sideDenominator := by exact_mod_cast hb.2
  unfold scale
  positivity

theorem target_factor (a b : Reference) (n : Direction) :
    target a b n = ⟨scale a b*n.x, scale a b*n.y, (target a b n).constant⟩ := by
  unfold target scale
  congr 1 <;> ring

def PairCheck {r : Nat} {rows : Fin r → Row} (a b : Context rows)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat) : Prop :=
  ∀ i : Fin 8,
    let n := direction a.reference b.reference i
    let A := (a.select (keys i)).val.basis
    let B := (b.select (opposite (keys i))).val.basis
    A.Cone n.x n.y ∧ B.Cone (-n.x) (-n.y) ∧
      VertexSupport.PairCheck A B n.x n.y (scale a.reference b.reference)
        (target a.reference b.reference n).constant

instance {r : Nat} {rows : Fin r → Row} (a b : Context rows)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat) :
    Decidable (PairCheck a b keys opposite) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, _ ∧ _))

theorem pair_sound {r : Nat} {rows : Fin r → Row} (a b : Context rows)
    (ha : a.reference.Valid) (hb : b.reference.Valid)
    (hac : a.reference.value.Check) (hbc : b.reference.value.Check)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : PairCheck a b keys opposite) (p q : Fin 2 → ℝ)
    (hp : ∀ i ∈ a.inputs, (rows i).Holds p)
    (hq : ∀ i ∈ b.inputs, (rows i).Holds q) :
    S12.OverlapsAt (a.reference.value.toSquare hac) (b.reference.value.toSquare hbc)
      (p 0,p 1) (q 0,q 1) := by
  apply ReferenceAxis.overlap a.reference b.reference ha hb hac hbc p q
  intro n hn
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hn
  let j : Fin 8 := ⟨i.val, by simpa [directions] using i.isLt⟩
  have he : direction a.reference b.reference j = n := by
    simpa [direction,j] using hi
  rw [← he, target_factor]
  obtain ⟨coneA,coneB,bound⟩ := checked j
  let A := a.select (keys j)
  let B := b.select (opposite (keys j))
  apply VertexSupport.pair_sound A.val.basis B.val.basis
    A.property.2.2.2.2 B.property.2.2.2.2 _ _ _ _ (scale_positive _ _ ha hb) bound p q
  · exact A.support _ _ coneA p hp
  · exact B.support _ _ coneB q hq

#print axioms pair_sound

end N12Compact.CachedSupportFan
