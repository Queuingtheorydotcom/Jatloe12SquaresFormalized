import Compact.Cases.C898.CachedPairs.Step11Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep11_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_11 q)
    (ht : OrientedPoseCovered continuousScout898Domain0_9 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_12 q := by
  exact pairStep11_geometric_sound q t hq ht disjoint
#print axioms pairStep11_sound

end
end N12Compact.C898Cached.AllPairs
