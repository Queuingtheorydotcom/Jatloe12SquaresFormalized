import Compact.Cases.C898.CachedPairs.Step05Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep5_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain7_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain6_5 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain7_6 q := by
  exact pairStep5_geometric_sound q t hq ht disjoint
#print axioms pairStep5_sound

end
end N12Compact.C898Cached.AllPairs
