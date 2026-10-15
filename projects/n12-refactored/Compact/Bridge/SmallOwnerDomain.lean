import S12.DirectSingleDomain

/-! A cardinality bound of two reduces the auxiliary owner check to56 sets.
The original1024-subset statement follows symbolically; no original owner
pattern or certified local refutation is removed. Cached signatures contain
only the fields used by the ownership check, with an exact equality to the
original proof-bearing query list. -/

set_option Elab.async false

namespace N12Compact.SmallOwnerDomain
open S12

private theorem clique_subset {M : Type} [DecidableEq M]
    (compatible : M → M → Prop) [DecidableRel compatible]
    (vertices : List M) (group : Finset M)
    (member : group ∈ cliques compatible vertices) :
    ∀ i ∈ group, i ∈ vertices := by
  induction vertices generalizing group with
  | nil =>
      have empty : group = ∅ := by simpa only [cliques, List.mem_singleton] using member
      subst group
      simp
  | cons first rest ih =>
      change group ∈ cliques compatible rest ++
        ((cliques compatible rest).filter fun g => decide (∀ j ∈ g, compatible first j)).map
          (insert first) at member
      intro i hi
      rcases List.mem_append.mp member with old | added
      · exact List.mem_cons_of_mem _ (ih group old i hi)
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp added
        rcases Finset.mem_insert.mp hi with same | later
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem _ (ih g (List.mem_filter.mp hg).1 i later)

def smallSubsets : List (Finset Nat) :=
  ([∅] ++ (List.range 10).map (fun i => {i})) ++
    (List.range 10).flatMap (fun i =>
      ((List.range 10).filter (fun j => decide (i < j))).map (fun j => {i,j}))

private theorem pair_mem (i j : Nat) (hi : i < 10) (hj : j < 10) (hne : i ≠ j) :
    {i,j} ∈ smallSubsets := by
  have increasing : ∀ a b : Nat, a < 10 → b < 10 → a < b →
      {a,b} ∈ smallSubsets := by
    intro a b ha hb hab
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨a, List.mem_range.mpr ha, List.mem_map.mpr ⟨b, ?_, rfl⟩⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hb, decide_eq_true hab⟩
  by_cases ordered : i < j
  · exact increasing i j hi hj ordered
  · have ordered' : j < i := by omega
    simpa only [Finset.pair_comm] using increasing j i hj hi ordered'

theorem smallSubsets_complete (s : Finset Nat) (subset : s ⊆ Finset.range 10)
    (small : s.card ≤ 2) : s ∈ smallSubsets := by
  by_cases empty : s.card = 0
  · have hs := Finset.card_eq_zero.mp empty
    subst s
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_cons_self
  by_cases singleton : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp singleton
    have hi : i < 10 := Finset.mem_range.mp (subset (Finset.mem_singleton_self i))
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  · have two : s.card = 2 := by omega
    obtain ⟨i,j,hne,rfl⟩ := Finset.card_eq_two.mp two
    exact pair_mem i j
      (Finset.mem_range.mp (subset (by simp)))
      (Finset.mem_range.mp (subset (by simp))) hne

abbrev Signature := Nat × Fin 3 × Finset Nat

def signature (query : LocalQuery) : Signature :=
  (query.mask,query.kind,query.owned)

def Check (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Prop :=
  w.lower = (if w.mask ∈ auxExempt kind then 0 else 1) ∧
  w.upper = (family ∩ auxExempt kind).card - 2 + w.lower ∧
  ∀ owned ∈ smallSubsets, w.lower ≤ owned.card → owned.card ≤ w.upper →
    owned ∈ w.allowed ∨ (w.mask,auxKind kind,owned) ∈ signatures

instance (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Decidable (Check w family kind signatures) := by
  unfold Check
  letI : Decidable (∀ owned ∈ smallSubsets, w.lower ≤ owned.card → owned.card ≤ w.upper →
      owned ∈ w.allowed ∨ (w.mask,auxKind kind,owned) ∈ signatures) :=
    List.decidableBAll _ smallSubsets
  infer_instance

theorem checked (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature)
    (exact_signatures : signatures = w.queries.map (fun q => signature q.val))
    (upper : w.upper ≤ 2) (check : Check w family kind signatures) :
    w.Check family kind := by
  refine ⟨check.1,check.2.1,?_⟩
  intro owned member low high
  have subset : owned ⊆ Finset.range 10 := by
    intro i hi
    exact Finset.mem_range.mpr (List.mem_range.mp
      (clique_subset (fun _ _ : Nat => True) (List.range 10) owned member i hi))
  have small := smallSubsets_complete owned subset (high.trans upper)
  rcases check.2.2 owned small low high with allowed | excluded
  · exact Or.inl allowed
  · rw [exact_signatures] at excluded
    obtain ⟨q, member, equal⟩ := List.mem_map.mp excluded
    have first := Prod.mk.inj equal
    have second := Prod.mk.inj first.2
    exact Or.inr ⟨q,member,first.1,second.1,second.2⟩

#print axioms smallSubsets_complete
#print axioms checked
end N12Compact.SmallOwnerDomain
