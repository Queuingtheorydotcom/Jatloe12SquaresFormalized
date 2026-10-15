import Compact.Cases.C898.CachedPairs.Step12Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep12_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_12 q)
    (ht : OrientedPoseCovered continuousScout898Domain6_5 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_13 q := by
  exact pairStep12_geometric_sound q t hq ht disjoint
#print axioms pairStep12_sound

end
end N12Compact.C898Cached.AllPairs
