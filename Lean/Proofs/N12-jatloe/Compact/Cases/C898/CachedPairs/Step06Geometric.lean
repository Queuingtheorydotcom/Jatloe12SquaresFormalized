import Compact.Cases.C898.CachedPairs.Step06Metadata
import Compact.Cases.C898.CachedPairs.Step06CommonGroups

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section
theorem pairStep6_geometric_sound (q t : S12Pilot.OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain7_6 q)
    (ht : OrientedPoseCovered continuousScout898Domain11_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain7_7 q := by
  have hp := step_sound_of_overlap continuousScout898Domain7_6Ids continuousScout898Domain11_0Ids
    step6Pieces step6Plans complement step6Sources step6Neighbors
    step6_cover step6_plans_checked step6_source_matches
    step6_neighbor_complete step6_geometric_overlap
    q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step6_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms pairStep6_geometric_sound

end
end N12Compact.C898Cached.AllPairs
