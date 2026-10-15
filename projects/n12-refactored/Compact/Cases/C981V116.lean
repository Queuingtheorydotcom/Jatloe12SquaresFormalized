import Compact.Geometry.C981Midpoint
import Completion.Cases.C981.VectorData

/-!
Original C981 representative 116, with its exact owner assignment. This
symbolic proof replaces the entire historical InitialV116 certificate;
the historical 32 angle roots and region trees are not imported.
-/

namespace N12Compact.C981V116

open S12 S12Pilot S12Completion.C981

def vector : Fin 12 → Finset Nat :=
  ![{2,12},{0,10},∅,{7,19},∅,{4,16},{9,17},{5,13},{1,11},{6,15},{8,18},{3,14}]

/-- Whole original vector exclusion, derived directly from six ownership
facts and the packing's actual disjointness. -/
theorem excluded : ExcludesVector (List.ofFn vector) := by
  intro p hf hv
  apply C981Midpoint.excludes (owners p 6) (owners p 3) (owners_side_gt p 6)
  · exact owners_query_inside p vector hf hv 6 _ (by decide)
  · exact owners_query_inside p vector hf hv 6 _ (by decide)
  · exact owners_query_outside p vector hf hv 6 _ (by decide)
  · exact owners_query_outside p vector hf hv 6 _ (by decide)
  · exact owners_query_inside p vector hf hv 3 _ (by decide)
  · exact owners_query_inside p vector hf hv 3 _ (by decide)
  · exact owners_disjoint p hf 6 3 (by decide)

/-- Bind to the original 117-row catalogue, without editing that catalogue. -/
theorem representative116_excluded : ExcludesVector (representativeVectors[116]!) := by
  have he : representativeVectors[116]! = List.ofFn vector := rfl
  rw [he]
  exact excluded

#print axioms representative116_excluded

end N12Compact.C981V116
