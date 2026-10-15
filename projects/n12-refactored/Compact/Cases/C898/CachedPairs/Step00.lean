import Compact.Cases.C898.CachedPairs.Step00Geometric

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

theorem pairStep0_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain1_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain8_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain1_1 q := by
  exact pairStep0_geometric_sound q t hq ht disjoint
#print axioms pairStep0_sound

end
end N12Compact.C898Cached.AllPairs
