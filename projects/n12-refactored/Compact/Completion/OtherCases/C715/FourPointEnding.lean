import S12.ShortCluster

/-! The first eight C715 ownership alternatives have one common four-point
obstruction. All sixteen excluding-face choices, including contact, are
retained. The only metric bound is the exact short projection of the two
excluded points; no angle restriction or side upper bound is used. -/

namespace N12Compact.Completion.OtherCases.C715
open S12 S12Pilot
set_option Elab.async false

theorem four_point_ending (W : OpenSquare) (side : 1 < W.side)
    (a : W.Inside 2 (113/50)) (b : W.Inside 3 (8/5)) :
    W.Inside (113/50) 2 ∨ W.Inside 3 (113/50) := by
  obtain ⟨a₀,a₁,a₂,a₃⟩ := a
  obtain ⟨b₀,b₁,b₂,b₃⟩ := b
  obtain ⟨d₀,d₁,d₂,d₃⟩ := short_projections W
    (113/50 - 3) (2 - 113/50) (by norm_num)
  by_contra missing
  obtain ⟨p,q⟩ := not_or.mp missing
  simp only [OpenSquare.Inside,InBands,not_and_or,not_lt] at p q
  rcases p with p | p | p | p <;>
    rcases q with q | q | q | q <;>
    linarith only [side,a₀,a₁,a₂,a₃,b₀,b₁,b₂,b₃,d₀,d₁,d₂,d₃,p,q]

end N12Compact.Completion.OtherCases.C715
