import Completion.Cases.C977.MissingCornerPoints

namespace S12Completion.C977
open S12 S12Pilot

/-- The four singleton wall codes, in left, bottom, right, top order. -/
def wallCode (k : Fin 4) : Nat :=
  ![4096, 8192, 16384, 32768] k

theorem wall_code_mem (k : Fin 4) : wallCode k ∈ family := by
  fin_cases k <;> decide

theorem wall_code_injective : Function.Injective wallCode := by decide

/-- Original square labels for all four wall owners. Nothing is relabeled. -/
structure WallOwners (p : NormalizedPacking) where
  index : Fin 4 → Fin 12
  code : ∀ k, markerCode p (index k) = wallCode k

theorem WallOwners.index_injective {p : NormalizedPacking} (w : WallOwners p) :
    Function.Injective w.index := by
  intro k l h
  apply wall_code_injective
  exact (w.code k).symm.trans ((congrArg (markerCode p) h).trans (w.code l))

/-- Extract the four distinct wall owners from the entire actual family. -/
theorem wall_owners (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    Nonempty (WallOwners p) := by
  classical
  have h : ∀ k : Fin 4, ∃ i : Fin 12, markerCode p i = wallCode k := by
    intro k
    have hm : wallCode k ∈ codedMarkerFamily p := by
      rw [hf]
      exact wall_code_mem k
    obtain ⟨i, hi, _⟩ := code_owner_unique p (wallCode k) hm
    exact ⟨i, hi⟩
  exact ⟨⟨fun k => Classical.choose (h k), fun k => Classical.choose_spec (h k)⟩⟩

/-- The left/right owners split their vertical center coordinate; the
    bottom/top owners split their horizontal center coordinate. -/
noncomputable def wallCoordinate (p : NormalizedPacking) (w : WallOwners p) (k : Fin 4) : ℝ :=
  if k.val % 2 = 0 then centerY (p.square (w.index k))
  else centerX (p.square (w.index k))

/-- Each coordinate has two closed half-spaces. True selects the lower one. -/
abbrev WallBranch := Fin 4 → Bool

def WallHalfSpaces (p : NormalizedPacking) (w : WallOwners p)
    (b : WallBranch) : Prop :=
  ∀ k, if b k then wallCoordinate p w k ≤ 2 else 2 ≤ wallCoordinate p w k

theorem wall_branch_count : Fintype.card WallBranch = 16 := by decide

/-- Every orientation and every center occurs in a closed wall branch.
    No geometric pruning or enumeration certificate is assumed. -/
theorem closed_wall_branch_cover (p : NormalizedPacking) (w : WallOwners p) :
    ∃ b : WallBranch, WallHalfSpaces p w b := by
  classical
  refine ⟨fun k => decide (wallCoordinate p w k ≤ 2), ?_⟩
  intro k
  by_cases h : wallCoordinate p w k ≤ 2
  · simp [h]
  · simpa only [h, decide_false, Bool.false_eq_true, ite_false] using
      (le_of_not_ge h : 2 ≤ wallCoordinate p w k)

/-- Equality is retained by both choices, even when the other coordinates
    choose different branches. -/
theorem wall_split_tie (p : NormalizedPacking) (w : WallOwners p) (k : Fin 4)
    (h : wallCoordinate p w k = 2) (choice : Bool) :
    if choice then wallCoordinate p w k ≤ 2 else 2 ≤ wallCoordinate p w k := by
  cases choice <;> simp [h]

/-- All wall owners and one of the sixteen closed branches are available
    for every actual case-977 packing. This is coverage, not exclusion. -/
theorem case_wall_branch_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ w : WallOwners p, ∃ b : WallBranch, WallHalfSpaces p w b := by
  obtain ⟨w⟩ := wall_owners p hf
  obtain ⟨b, hb⟩ := closed_wall_branch_cover p w
  exact ⟨w, b, hb⟩

/-- Marker 10 is genuinely unused: no original owner has it strictly inside.
    This follows from every member of the family, not a chosen labeling. -/
theorem unused_marker_ten (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ¬Owns (p.square i) 10 := by
  have hfinite : ∀ m ∈ family, (10 : Marker) ∉ maskSupport m := by decide
  have hm : markerCode p i ∈ family := by
    rw [← hf]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  intro ho
  exact hfinite _ hm ((coded_exact p i 10).mp ho)

end S12Completion.C977
