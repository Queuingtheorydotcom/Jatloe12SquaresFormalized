import Compact.Bridge.IndexedCommonGroups

/-! Exhaustive rectangular coverage follows from binary subdivision.
Only the leaves are matched to checked groups. The proof size is proportional
to the number of groups, independently of the Cartesian number of pose pairs.
-/

set_option Elab.async false

namespace N12Compact.IndexedCommonGroups

inductive RectanglePartition where
  | leaf
  | sourceCut (offset : Nat) (left right : RectanglePartition)
  | neighborCut (offset : Nat) (left right : RectanglePartition)

namespace RectanglePartition

def sourceLeft (box : Scope) (offset : Nat) : Scope :=
  ⟨box.sourceStart, offset, box.neighborStart, box.neighborCount⟩

def sourceRight (box : Scope) (offset : Nat) : Scope :=
  ⟨box.sourceStart + offset, box.sourceCount - offset,
    box.neighborStart, box.neighborCount⟩

def neighborLeft (box : Scope) (offset : Nat) : Scope :=
  ⟨box.sourceStart, box.sourceCount, box.neighborStart, offset⟩

def neighborRight (box : Scope) (offset : Nat) : Scope :=
  ⟨box.sourceStart, box.sourceCount,
    box.neighborStart + offset, box.neighborCount - offset⟩

def Check : RectanglePartition → Scope → List Scope → Prop
  | .leaf, box, scopes => box ∈ scopes
  | .sourceCut offset left right, box, scopes =>
      0 < offset ∧ offset < box.sourceCount ∧
        left.Check (sourceLeft box offset) scopes ∧
        right.Check (sourceRight box offset) scopes
  | .neighborCut offset left right, box, scopes =>
      0 < offset ∧ offset < box.neighborCount ∧
        left.Check (neighborLeft box offset) scopes ∧
        right.Check (neighborRight box offset) scopes

noncomputable instance (tree : RectanglePartition) (box : Scope) (scopes : List Scope) :
    Decidable (tree.Check box scopes) := by
  induction tree generalizing box with
  | leaf => exact inferInstanceAs (Decidable (box ∈ scopes))
  | sourceCut offset left right ihl ihr =>
      letI := ihl (sourceLeft box offset)
      letI := ihr (sourceRight box offset)
      exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
  | neighborCut offset left right ihl ihr =>
      letI := ihl (neighborLeft box offset)
      letI := ihr (neighborRight box offset)
      exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem sound (tree : RectanglePartition) (box : Scope) (scopes : List Scope)
    (checked : tree.Check box scopes) (i j : Nat) (inside : box.Covers i j) :
    ScopeCheck scopes i j := by
  induction tree generalizing box with
  | leaf => exact ⟨box, checked, inside⟩
  | sourceCut offset left right ihl ihr =>
      change 0 < offset ∧ offset < box.sourceCount ∧
        left.Check (sourceLeft box offset) scopes ∧
        right.Check (sourceRight box offset) scopes at checked
      by_cases before : i < box.sourceStart + offset
      · apply ihl (sourceLeft box offset) checked.2.2.1
        rcases inside with ⟨lo, _, jlo, jhi⟩
        exact ⟨lo, before, jlo, jhi⟩
      · apply ihr (sourceRight box offset) checked.2.2.2
        rcases inside with ⟨ilo, ihi, jlo, jhi⟩
        change box.sourceStart + offset ≤ i ∧
          i < box.sourceStart + offset + (box.sourceCount - offset) ∧
          box.neighborStart ≤ j ∧ j < box.neighborStart + box.neighborCount
        have bound := checked.2.1
        omega
  | neighborCut offset left right ihl ihr =>
      change 0 < offset ∧ offset < box.neighborCount ∧
        left.Check (neighborLeft box offset) scopes ∧
        right.Check (neighborRight box offset) scopes at checked
      by_cases before : j < box.neighborStart + offset
      · apply ihl (neighborLeft box offset) checked.2.2.1
        rcases inside with ⟨ilo, ihi, jlo, _⟩
        exact ⟨ilo, ihi, jlo, before⟩
      · apply ihr (neighborRight box offset) checked.2.2.2
        rcases inside with ⟨ilo, ihi, jlo, jhi⟩
        change box.sourceStart ≤ i ∧ i < box.sourceStart + box.sourceCount ∧
          box.neighborStart + offset ≤ j ∧
          j < box.neighborStart + offset + (box.neighborCount - offset)
        have bound := checked.2.1
        omega

theorem covers {u v : Nat} (tree : RectanglePartition) (scopes : List Scope)
    (checked : tree.Check ⟨0,u,0,v⟩ scopes) (i : Fin u) (j : Fin v) :
    ScopeCheck scopes i.val j.val :=
  tree.sound ⟨0,u,0,v⟩ scopes checked i.val j.val
    ⟨Nat.zero_le _, by simpa only [Nat.zero_add] using i.isLt,
      Nat.zero_le _, by simpa only [Nat.zero_add] using j.isLt⟩

#print axioms sound
#print axioms covers
end RectanglePartition
end N12Compact.IndexedCommonGroups
