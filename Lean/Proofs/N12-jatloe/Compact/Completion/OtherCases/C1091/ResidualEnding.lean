import Compact.Completion.OtherCases.C1091.ResidualNoTopG4
import Compact.Completion.OtherCases.C1091.ResidualTopG4

/-! Complete raw residual ending in C1091-complete-proof. Its only case
split is actual top ownership of G4, and both branches have proof bodies.
The original-family producer of the residual input remains separate. -/
namespace N12Compact.Completion.OtherCases.C1091.Residual
open S12 S12Pilot
set_option Elab.async false

theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False := by
  by_cases top : (q 11).Inside (87/50) 3
  · exact top_g4_impossible q h top
  · exact no_top_g4_impossible q h top

#print axioms impossible
end N12Compact.Completion.OtherCases.C1091.Residual
