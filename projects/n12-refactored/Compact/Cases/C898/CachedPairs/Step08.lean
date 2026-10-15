import Compact.Cases.C898.CachedPairs.Step08Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep8_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain0_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain1_1 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain0_9 q := by
  exact pairStep8_geometric_sound q t hq ht disjoint
#print axioms pairStep8_sound

end
end N12Compact.C898Cached.AllPairs
