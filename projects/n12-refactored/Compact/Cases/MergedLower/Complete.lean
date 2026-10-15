import Compact.Cases.MergedLower.Domains7180
import Compact.Cases.MergedLower.Domains589590
import Compact.Cases.MergedLower.Recipes

/-! Complete source exclusions of original families71,80,589,590.
Only two symbolic arguments and their reflections are used. All finite
ownership coverage is rechecked from certified original-domain specifications.
Source assembly is not a report of a completed Lean replay. -/
namespace N12Compact.MergedLower
open S12 FourSquareVectorCover
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem cover71 : Check domains71 recipes := by
  apply check_of_parts domains71 recipes
  · simp only [recipes, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    dsimp only [upperNE, upperNW, spanNE, spanNW]
    decide +kernel
  · decide +kernel

theorem case71_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family71) : False :=
  impossible domains71 domains71_members domains71_distinct recipes cover71 p hf

theorem cover80 : Check domains80 recipes := by
  apply check_of_parts domains80 recipes
  · simp only [recipes, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    dsimp only [upperNE, upperNW, spanNE, spanNW]
    decide +kernel
  · decide +kernel

theorem case80_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family80) : False :=
  impossible domains80 domains80_members domains80_distinct recipes cover80 p hf

theorem cover589 : Check domains589 recipes := by
  apply check_of_parts domains589 recipes
  · simp only [recipes, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    dsimp only [upperNE, upperNW, spanNE, spanNW]
    decide +kernel
  · decide +kernel

theorem case589_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family589) : False :=
  impossible domains589 domains589_members domains589_distinct recipes cover589 p hf

theorem cover590 : Check domains590 recipes := by
  apply check_of_parts domains590 recipes
  · simp only [recipes, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    dsimp only [upperNE, upperNW, spanNE, spanNW]
    decide +kernel
  · decide +kernel

theorem case590_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family590) : False :=
  impossible domains590 domains590_members domains590_distinct recipes cover590 p hf

#print axioms case71_impossible
#print axioms case80_impossible
#print axioms case589_impossible
#print axioms case590_impossible
end N12Compact.MergedLower
