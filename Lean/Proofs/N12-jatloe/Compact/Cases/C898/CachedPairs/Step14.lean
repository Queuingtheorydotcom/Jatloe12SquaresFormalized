import Compact.Cases.C898.PairStep14CommonPoint

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

theorem pairStep14_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_14 q)
    (ht : OrientedPoseCovered continuousScout898Domain9_8 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_15 q :=
  N12Compact.C898Cached.TerminalCommon.pairStep14_common_sound q t hq ht disjoint

#print axioms pairStep14_sound

end
end N12Compact.C898Cached.AllPairs
