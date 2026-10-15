import Compact.Cases.C898.CachedPairs.Step03Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep3_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain6_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain3_3 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain6_4 q := by
  exact pairStep3_geometric_sound q t hq ht disjoint
#print axioms pairStep3_sound

end
end N12Compact.C898Cached.AllPairs
