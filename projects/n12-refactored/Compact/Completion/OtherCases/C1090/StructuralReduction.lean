import Compact.Completion.OtherCases.C1090.StructuralGeometry
import Compact.Completion.OtherCases.C1090.EarlyResidual

/-! C1090-SIMPLIFIED-PROOF sections 7--8, reduced directly by the literal
F/G covering alternatives. The five geometric exclusions need no exact
numeric SE/NE label disjunction: the ordinary covering disjunctions in
Early.Input suffice. Consequently there is no stored catalogue trace or
assumed support box in this join.

This is a continuous exclusion conditional on Early.Input. Its original
packing producer must still establish the compulsory auxiliary points,
covering alternatives and the explicit topComponent consequence. No
ExcludesCase declaration or complete finite-entrance verification is claimed.
All sources remain uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.Structural
open S12 S12Pilot
set_option Elab.async false

/-- The outward S alternative is impossible for either literal northeast
F5 choice. The F7 branch follows from the genuine local F cover. -/
theorem southeast_g6 (q : Fin 12 → OpenSquare) (h : Early.PointTable q) :
    (q 5).Inside (113/50) 2 := by
  by_contra missing
  by_cases f5 : (q 6).Inside 2 (113/50)
  · exact outward_mixed_impossible q h missing f5
  · exact outward_top_only_impossible q h missing
      ((northeast_f5_or_f7 q h).resolve_left f5) f5

/-- Omitting northeast F7 would give the eliminated F5/G7 elbow.
Neither an exact auxiliary label nor an angle choice is used. -/
theorem northeast_f7 (q : Fin 12 → OpenSquare) (h : Early.PointTable q) :
    (q 6).Inside (12/5) 3 := by
  by_contra missing
  exact northeast_elbow_impossible q h
    ((northeast_f5_or_f7 q h).resolve_right missing) missing

/-- The two residual point profiles have the same compulsory F7/G7
in E and F8/G6/G8 in S. E may or may not own F5; S cannot own F5,
and E cannot own G6 because its actual owner is S. This statement does
not identify complete auxiliary labels beyond these proved memberships. -/
theorem central_points (q : Fin 12 → OpenSquare) (h : Early.PointTable q) :
    (q 5).Inside (113/50) 2 ∧ (q 6).Inside (12/5) 3 ∧
      ¬(q 5).Inside 2 (113/50) ∧ ¬(q 6).Inside (113/50) 2 := by
  have sg6 := southeast_g6 q h
  exact ⟨sg6,northeast_f7 q h,
    fun own => southeast_f5_impossible q h sg6 own,
    fun own => h.apart 6 5 (by decide) _ _ ⟨own,sg6⟩⟩

/-- Every field of the continuous residual theorem now follows from the
actual early point table. The merged-left segment supplies its required
F0/G0, while the singleton keeps its separate horizontal seed. -/
theorem residual_input (q : Fin 12 → OpenSquare) (h : Early.PointTable q) :
    Residual.Input q :=
  Early.residual_input q h (southeast_g6 q h) (northeast_f7 q h)

/-- Complete continuous implication after the honest finite-entrance
interface. Both northeast F5 possibilities and every square orientation
are handled by Residual.impossible after the structural point reduction. -/
theorem impossible_of_early_input (q : Fin 12 → OpenSquare) (h : Early.Input q) : False :=
  Residual.impossible q (residual_input q (Early.point_table q h))

#print axioms central_points
#print axioms residual_input
#print axioms impossible_of_early_input
end N12Compact.Completion.OtherCases.C1090.Structural
