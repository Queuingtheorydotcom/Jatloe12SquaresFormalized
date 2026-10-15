import Compact.Cases.C898.CachedPairs.Step11Metadata
import Compact.Cases.C898.CachedPairs.Step11CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep11_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_11 q)
    (ht : OrientedPoseCovered continuousScout898Domain0_9 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_12 q := by
  have hp := step_sound_of_overlap continuousScout898Domain5_11Ids continuousScout898Domain0_9Ids
    step11Pieces step11Plans complement step11Sources step11Neighbors
    step11_cover step11_plans_checked step11_source_matches
    step11_neighbor_complete step11_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step11_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep11_geometric_sound

end
end N12Compact.C898Cached.AllPairs
