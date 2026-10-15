import Compact.Cases.C898.CachedPairs.Step00Metadata
import Compact.Cases.C898.CachedPairs.Step00CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep0_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain1_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain8_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain1_1 q := by
  have hp := step_sound_of_overlap continuousScout898Domain1_0Ids continuousScout898Domain8_0Ids
    step0Pieces step0Plans complement step0Sources step0Neighbors
    step0_cover step0_plans_checked step0_source_matches
    step0_neighbor_complete step0_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step0_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep0_geometric_sound

end
end N12Compact.C898Cached.AllPairs
