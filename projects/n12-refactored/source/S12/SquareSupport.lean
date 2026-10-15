import S12.SquareSupportBase
import S12.SquareSeparation
namespace S12
noncomputable section
open S12Pilot

/-- Disjoint interiors imply a nonzero support-gap inequality, including touching cases. -/
theorem square_support_separator (q r : OpenSquare)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    ∃ nx ny : ℝ,(nx≠0 ∨ ny≠0) ∧
      squareRadius q nx ny+squareRadius r nx ny≤
        nx*(centerX r-centerX q)+ny*(centerY r-centerY q) := by
  obtain ⟨nx,ny,u,hn,hq,hr⟩ := square_linear_separator q r hd
  have hq' := square_support_bound q nx ny u (fun x y hi => le_of_lt (hq x y hi))
  have hr' := square_support_bound r (-nx) (-ny) (-u) (by
    intro x y hi
    have hh := hr x y hi
    linarith)
  rw [squareRadius_neg] at hr'
  exact ⟨nx,ny,hn,by linarith⟩

#print axioms square_support_separator
end
end S12
