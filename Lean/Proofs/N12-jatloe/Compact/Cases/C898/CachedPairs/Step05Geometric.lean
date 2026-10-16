import Compact.Cases.C898.CachedPairs.Step05Metadata
import Compact.Cases.C898.CachedPairs.Step05CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep5_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain7_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain6_5 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain7_6 q := by
  have hp := step_sound_of_overlap continuousScout898Domain7_0Ids continuousScout898Domain6_5Ids
    step5Pieces step5Plans complement step5Sources step5Neighbors
    step5_cover step5_plans_checked step5_source_matches
    step5_neighbor_complete step5_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step5_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep5_geometric_sound

end
end N12Compact.C898Cached.AllPairs
