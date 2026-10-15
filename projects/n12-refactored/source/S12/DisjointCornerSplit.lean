import S12.Diagonal

/-! Elementary original disjointness split, factored verbatim from MissingCornerBranches. -/
namespace S12
open S12Pilot

/-- A complete corner split, including the possibility that neither square
contains the point. It requires only their already-proved disjointness. -/
theorem disjoint_corner_split (q r : OpenSquare) (x y : ℝ)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    (¬q.Inside x y) ∨ (q.Inside x y ∧ ¬r.Inside x y) := by
  by_cases h : q.Inside x y
  · exact Or.inr ⟨h,fun hr => hd x y ⟨h,hr⟩⟩
  · exact Or.inl h


end S12
