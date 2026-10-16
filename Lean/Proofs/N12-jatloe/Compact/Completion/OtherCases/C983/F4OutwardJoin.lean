import Compact.Completion.OtherCases.C983.F4CentralEntrance
import Compact.Completion.OtherCases.C983.ActualOutwardPair

/-! The original C983 F4 join to the complete actual outward-pair theorem.
No ownership of an auxiliary omitted by this southeast square is guessed. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem outward_exact_check :
    ∀ owned∈originalComponents 5,4∉owned → 16∉owned → owned={8,18} := by decide +kernel

theorem f4_southeast_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : 16∈actual p 5 := by
  by_contra noG6
  have outward := outward_exact_check _ (original_actual_mem p hf 5)
    (absent_of_foreign p hf 7 5 4 (by decide +kernel) f4) noG6
  have f8 : 8∈actual p 5 := by rw [outward]; decide +kernel
  have g8 : 18∈actual p 5 := by rw [outward]; decide +kernel
  exact southeast_outward_pair_exclusion p hf f8 g8 noG6
    (f4_outward_northeast_f5 p hf f4 noG6) (f4_northeast_g7 p hf f4)
    (f4_top_origin p hf f4)

end
#print axioms f4_southeast_g6
end N12Compact.Completion.OtherCases.C983

