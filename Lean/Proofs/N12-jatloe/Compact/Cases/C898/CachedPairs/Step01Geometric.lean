import Compact.Cases.C898.CachedPairs.Step01Metadata
import Compact.Cases.C898.CachedPairs.Step01CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep1_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain2_0 q)
    (ht : OrientedPoseCovered continuousScout898Domain10_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain2_2 q := by
  have hp := step_sound_of_overlap continuousScout898Domain2_0Ids continuousScout898Domain10_0Ids
    step1Pieces step1Plans complement step1Sources step1Neighbors
    step1_cover step1_plans_checked step1_source_matches
    step1_neighbor_complete step1_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step1_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep1_geometric_sound

end
end N12Compact.C898Cached.AllPairs
