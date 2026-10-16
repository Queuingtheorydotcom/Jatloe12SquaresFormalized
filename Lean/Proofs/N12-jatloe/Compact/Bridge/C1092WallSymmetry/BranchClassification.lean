import Compact.Bridge.C1092WallSymmetry.Actions

/-! The sixteen wall-sign patterns, checked independently of physical transport.
Orbit disjointness is partitioned into the 64 pairs of container symmetries. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

theorem symmetry_mem (u : Fin 8) : symmetry u ∈ allTransforms := by
  fin_cases u <;> decide +kernel

/-- Only sixteen Boolean patterns are classified here. This is a symmetry
identity, not an angle or geometric case search. -/
theorem branch_coverage (b : WallBranch) :
    ∃ u : Fin 8, ∃ k : Fin 4, branchAction (symmetry u) b = canonicalBranch k := by
  have finite : ∀ b₀ b₁ b₂ b₃ : Bool, ∃ u : Fin 8, ∃ k : Fin 4, ∀ j : Fin 4,
      branchAction (symmetry u) ![b₀,b₁,b₂,b₃] j = canonicalBranch k j := by
    intro b₀ b₁ b₂ b₃
    cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide +kernel
  have reconstruct : b = ![b 0,b 1,b 2,b 3] := by
    funext j; fin_cases j <;> rfl
  obtain ⟨u,k,h⟩ := finite (b 0) (b 1) (b 2) (b 3)
  exact ⟨u,k,by rw [reconstruct]; exact funext h⟩

/-- No two of the four displayed types share a transformed Boolean
pattern. This small finite fact makes the four-way split irredundant. -/
theorem canonical_orbits_disjoint : ∀ u v : Fin 8, ∀ i j : Fin 4,
    (∀ k : Fin 4,
      branchAction (symmetry u) (canonicalBranch i) k =
      branchAction (symmetry v) (canonicalBranch j) k) → i = j := by
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel

end N12Compact.C1092WallSymmetry
