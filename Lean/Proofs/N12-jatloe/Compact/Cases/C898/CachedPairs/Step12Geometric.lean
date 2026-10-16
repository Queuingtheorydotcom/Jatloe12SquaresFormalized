import Compact.Cases.C898.CachedPairs.Step12Metadata
import Compact.Cases.C898.CachedPairs.Step12CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep12_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain5_12 q)
    (ht : OrientedPoseCovered continuousScout898Domain6_5 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain5_13 q := by
  have hp := step_sound_of_overlap continuousScout898Domain5_12Ids continuousScout898Domain6_5Ids
    step12Pieces step12Plans complement step12Sources step12Neighbors
    step12_cover step12_plans_checked step12_source_matches
    step12_neighbor_complete step12_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step12_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep12_geometric_sound

end
end N12Compact.C898Cached.AllPairs
