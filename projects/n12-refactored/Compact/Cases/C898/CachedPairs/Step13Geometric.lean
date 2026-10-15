import Compact.Cases.C898.CachedPairs.Step13Metadata
import Compact.Cases.C898.CachedPairs.Step13CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep13_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_13 q)
    (ht : OrientedPoseCovered continuousScout898Domain7_7 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_14 q := by
  have hp := step_sound_of_overlap continuousScout898Domain5_13Ids continuousScout898Domain7_7Ids
    step13Pieces step13Plans complement step13Sources step13Neighbors
    step13_cover step13_plans_checked step13_source_matches
    step13_neighbor_complete step13_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step13_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep13_geometric_sound

end
end N12Compact.C898Cached.AllPairs
