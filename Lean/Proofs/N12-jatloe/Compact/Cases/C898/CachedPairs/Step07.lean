import Compact.Cases.C898.CachedPairs.Step07Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep7_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain9_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain2_2 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain9_8 q := by
  exact pairStep7_geometric_sound q t hq ht disjoint
#print axioms pairStep7_sound

end
end N12Compact.C898Cached.AllPairs
