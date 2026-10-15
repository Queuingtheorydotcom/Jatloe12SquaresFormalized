import S12.DomainEnumeration

/-! A checked sequence of small literal front covers replaces a single
large reduction of the complete ownership Cartesian product. Every compatible
extension is retained. The proposer of the literal tables is untrusted. -/
namespace N12Compact.PrefixCoverage
open S12
set_option Elab.async false

def StepCheck (before : List (List (Finset Nat)))
    (choices : List (Finset Nat)) (after : List (List (Finset Nat))) : Prop :=
  ∀ front ∈ before, ∀ x ∈ choices,
    (∀ y ∈ front, Disjoint x y) → front ++ [x] ∈ after

instance (before : List (List (Finset Nat))) (choices : List (Finset Nat))
    (after : List (List (Finset Nat))) : Decidable (StepCheck before choices after) := by
  unfold StepCheck
  infer_instance

inductive Chain : List (List (Finset Nat)) → List (List (Finset Nat)) →
    List (List (Finset Nat)) → Prop
  | nil (before) : Chain before [] before
  | cons {before next after choice choices} :
      StepCheck before choice next → Chain next choices after →
      Chain before (choice :: choices) after

theorem Chain.sound {before choices after} (chain : Chain before choices after)
    (front actual : List (Finset Nat)) (member : front ∈ before)
    (allowed : List.Forall₂ (fun x d => x ∈ d) actual choices)
    (pairwise : actual.Pairwise Disjoint)
    (apart : ∀ x ∈ actual, ∀ y ∈ front, Disjoint x y) :
    front ++ actual ∈ after := by
  induction chain generalizing front actual with
  | nil =>
      cases allowed
      simpa only [List.append_nil] using member
  | @cons before next after choice choices step tail ih =>
      cases allowed with
      | @cons x d xs ds hx hxs =>
          have hp := List.pairwise_cons.mp pairwise
          have extended : front ++ [x] ∈ next :=
            step front member x hx (fun y hy => apart x (by simp) y hy)
          have tailApart : ∀ z ∈ xs, ∀ y ∈ front ++ [x], Disjoint z y := by
            intro z hz y hy
            rcases List.mem_append.mp hy with old | last
            · exact apart z (List.mem_cons_of_mem x hz) y old
            · have equal : y = x := List.mem_singleton.mp last
              subst y
              exact (hp.1 z hz).symm
          simpa only [List.append_assoc, List.singleton_append] using
            ih (front ++ [x]) xs extended hxs hp.2 tailApart

theorem enumerate_valid (actual : List (Finset Nat))
    (choices : List (List (Finset Nat))) (used : Finset Nat)
    (member : actual ∈ enumerateAssignments choices used) :
    List.Forall₂ (fun x d => x ∈ d) actual choices ∧
      actual.Pairwise Disjoint ∧ ∀ x ∈ actual, Disjoint x used := by
  induction choices generalizing actual used with
  | nil =>
      have equal : actual = [] := by
        simpa only [enumerateAssignments, List.mem_singleton] using member
      subst actual
      exact ⟨List.Forall₂.nil, by simp, by simp⟩
  | cons choice choices ih =>
      obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp member
      by_cases apart : Disjoint x used
      · rw [if_pos apart] at h
        obtain ⟨xs, hxs, equal⟩ := List.mem_map.mp h
        subst actual
        have tail := ih xs (used ∪ x) hxs
        refine ⟨List.Forall₂.cons hx tail.1,
          List.pairwise_cons.mpr ⟨?_, tail.2.1⟩, ?_⟩
        · intro y hy
          exact ((Finset.disjoint_union_right.mp (tail.2.2 y hy)).2).symm
        · intro y hy
          rcases List.mem_cons.mp hy with same | later
          · subst y; exact apart
          · exact (Finset.disjoint_union_right.mp (tail.2.2 y later)).1
      · simp only [if_neg apart, List.not_mem_nil] at h

theorem cases_of_chain (choices : List (List (Finset Nat)))
    (targets cases : List (List (Finset Nat)))
    (chain : Chain [[]] choices targets)
    (covered : ∀ a ∈ targets, a ∈ cases) :
    ∀ a ∈ enumerateAssignments choices ∅, a ∈ cases := by
  intro a ha
  have valid := enumerate_valid a choices ∅ ha
  have final := chain.sound [] a (by simp) valid.1 valid.2.1 (by simp)
  exact covered a (by simpa only [List.nil_append] using final)

#print axioms cases_of_chain
end N12Compact.PrefixCoverage
