import Compact.Cases.C898.CachedPairs.Step06Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep6_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain7_6 q)
    (ht : OrientedPoseCovered continuousScout898Domain11_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain7_7 q := by
  exact pairStep6_geometric_sound q t hq ht disjoint
#print axioms pairStep6_sound

end
end N12Compact.C898Cached.AllPairs
