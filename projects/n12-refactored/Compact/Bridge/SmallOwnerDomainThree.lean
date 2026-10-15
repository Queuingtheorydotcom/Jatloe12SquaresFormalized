import Compact.Bridge.SmallOwnerDomain

/-! Exact owner-domain checks when the original upper bound is three.
The generic cardinality argument replaces the1024-subset enumeration by the
176 subsets of size at most three. Only mask/kind/owned signatures enter the
numeric check; their equality to the original proof-bearing query list is a
separate ordinary proof. No original ownership pattern is removed.
-/

set_option Elab.async false

namespace N12Compact.SmallOwnerDomainThree
open S12 SmallOwnerDomain

def triples : List (Finset Nat) :=
  (List.range 10).flatMap (fun a =>
    ((List.range 10).filter (fun b => decide (a < b))).flatMap (fun b =>
      ((List.range 10).filter (fun c => decide (b < c))).map (fun c => {a,b,c})))

def smallSubsetsThree : List (Finset Nat) := smallSubsets ++ triples

private theorem sorted_triple_mem (a b c : Nat) (ha : a < 10) (hb : b < 10)
    (hc : c < 10) (hab : a < b) (hbc : b < c) : {a,b,c} ∈ triples := by
  apply List.mem_flatMap.mpr
  refine ⟨a, List.mem_range.mpr ha, List.mem_flatMap.mpr ?_⟩
  refine ⟨b, List.mem_filter.mpr ⟨List.mem_range.mpr hb, decide_eq_true hab⟩,
    List.mem_map.mpr ?_⟩
  exact ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr hc, decide_eq_true hbc⟩, rfl⟩

private theorem triple_mem (a b c : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : {a,b,c} ∈ triples := by
  by_cases ab : a < b
  · by_cases bc : b < c
    · exact sorted_triple_mem a b c ha hb hc ab bc
    · have cb : c < b := by omega
      by_cases ac : a < c
      · have permutation : ({a,c,b} : Finset Nat) = {a,b,c} := by
          ext i; simp [or_comm, or_left_comm, or_assoc]
        simpa only [permutation] using sorted_triple_mem a c b ha hc hb ac cb
      · have ca : c < a := by omega
        have permutation : ({c,a,b} : Finset Nat) = {a,b,c} := by
          ext i; simp [or_comm, or_left_comm, or_assoc]
        simpa only [permutation] using sorted_triple_mem c a b hc ha hb ca ab
  · have ba : b < a := by omega
    by_cases ac : a < c
    · have permutation : ({b,a,c} : Finset Nat) = {a,b,c} := by
        ext i; simp [or_comm, or_left_comm, or_assoc]
      simpa only [permutation] using sorted_triple_mem b a c hb ha hc ba ac
    · have ca : c < a := by omega
      by_cases bc : b < c
      · have permutation : ({b,c,a} : Finset Nat) = {a,b,c} := by
          ext i; simp [or_comm, or_left_comm, or_assoc]
        simpa only [permutation] using sorted_triple_mem b c a hb hc ha bc ca
      · have cb : c < b := by omega
        have permutation : ({c,b,a} : Finset Nat) = {a,b,c} := by
          ext i; simp [or_comm, or_left_comm, or_assoc]
        simpa only [permutation] using sorted_triple_mem c b a hc hb ha cb ba

theorem smallSubsetsThree_complete (s : Finset Nat) (subset : s ⊆ Finset.range 10)
    (small : s.card ≤ 3) : s ∈ smallSubsetsThree := by
  by_cases two : s.card ≤ 2
  · exact List.mem_append_left _ (smallSubsets_complete s subset two)
  · have three : s.card = 3 := by omega
    obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp three
    apply List.mem_append_right
    apply triple_mem a b c
    · exact Finset.mem_range.mp (subset (by simp))
    · exact Finset.mem_range.mp (subset (by simp))
    · exact Finset.mem_range.mp (subset (by simp))
    · exact hab
    · exact hac
    · exact hbc

private theorem clique_subset {M : Type} [DecidableEq M]
    (compatible : M → M → Prop) [DecidableRel compatible]
    (vertices : List M) (group : Finset M)
    (member : group ∈ cliques compatible vertices) : ∀ i ∈ group, i ∈ vertices := by
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

def Check (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Prop :=
  w.lower = (if w.mask ∈ auxExempt kind then 0 else 1) ∧
  w.upper = (family ∩ auxExempt kind).card - 2 + w.lower ∧
  ∀ owned ∈ smallSubsetsThree, w.lower ≤ owned.card → owned.card ≤ w.upper →
    owned ∈ w.allowed ∨ (w.mask,auxKind kind,owned) ∈ signatures

instance (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Decidable (Check w family kind signatures) := by
  unfold Check
  letI : Decidable (∀ owned ∈ smallSubsetsThree, w.lower ≤ owned.card → owned.card ≤ w.upper →
      owned ∈ w.allowed ∨ (w.mask,auxKind kind,owned) ∈ signatures) :=
    List.decidableBAll _ smallSubsetsThree
  infer_instance

theorem checked (w : DirectSingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature)
    (exact_signatures : signatures = w.queries.map (fun q => signature q.val))
    (upper : w.upper ≤ 3) (check : Check w family kind signatures) : w.Check family kind := by
  refine ⟨check.1,check.2.1,?_⟩
  intro owned member low high
  have subset : owned ⊆ Finset.range 10 := by
    intro i hi
    exact Finset.mem_range.mpr (List.mem_range.mp
      (clique_subset (fun _ _ : Nat => True) (List.range 10) owned member i hi))
  have small := smallSubsetsThree_complete owned subset (high.trans upper)
  rcases check.2.2 owned small low high with allowed | excluded
  · exact Or.inl allowed
  · rw [exact_signatures] at excluded
    obtain ⟨q, member, equal⟩ := List.mem_map.mp excluded
    have first := Prod.mk.inj equal
    have second := Prod.mk.inj first.2
    exact Or.inr ⟨q,member,first.1,second.1,second.2⟩

#print axioms smallSubsetsThree_complete
#print axioms checked
end N12Compact.SmallOwnerDomainThree
