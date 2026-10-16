import Compact.Cases.C898.CachedPairs.Step04CommonPoints
import Compact.Cases.C898.CachedPairs.Step04Metadata
import Compact.Cases.C898.CachedCommonPoint
import Compact.Cases.C898.CachedGeometricPlans
import Compact.Core.RawSupportFanBridge

/-! Whole original Step04 through seven shared points and fourteen ordinary
fallback pairs. The conclusion retains all original source and neighbor
domains, outside-block pieces and exact outward-relaxation links. -/

set_option Elab.async false
set_option maxRecDepth 10000

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 S12Pilot IntegerSupport
noncomputable section

theorem step4_common_overlap (i : Fin 7) (j : Fin 64) (q t : OpenSquare)
    (hq : (poses (step4Sources i).pose).Realizes q)
    (ht : (poses (step4Neighbors j).pose).Realizes t)
    (block : ∀ k ∈ (step4Sources i).block, (rows k).Holds ![centerX q, centerY q]) :
    ∃ x y, q.Inside x y ∧ t.Inside x y := by
  have neighbor_block : ∀ k ∈ (step4Neighbors j).block,
      (rows k).Holds ![centerX t, centerY t] := by
    simp only [step4_neighbor_unblocked j, List.not_mem_nil, false_implies, forall_const]
  by_cases fallback : j.val < 2
  · have checked : step4RawPairCheck i j := by
      exact step4_fallback_pairs_checked i ⟨j.val, fallback⟩
    have original : (step4Sources i).PairCheck (step4Neighbors j) := by
      apply CachedSupportFan.PairCheck.of_cached_numeric
        (step4Sources i).context (step4Neighbors j).context
        (step4RawSources i) (step4RawNeighbors j)
        (step4RawSources_exact i) (step4RawNeighbors_exact j)
        (fanDirectionKey (step4Sources i).keyAngle (step4Neighbors j).keyAngle)
        (fun key => (key + 128) % 256)
      change RawSupportFan.PairCheck _ _ _ _ at checked
      simpa only [← step4RawSourceAngle_exact i, ← step4RawNeighborAngle_exact j] using checked
    exact (step4Sources i).pair_sound (step4Neighbors j) original q t hq ht block neighbor_block
  · let geometric : Fin 62 := ⟨j.val - 2, by omega⟩
    have neighbor_equal : step4GeometricNeighbor geometric = j := by
      apply Fin.ext
      dsimp only [step4GeometricNeighbor, geometric]
      omega
    let point := step4CommonPoints (step4PointGroup geometric)
    have source_inside : q.Inside point.value.1 point.value.2 :=
      (step4Sources i).point_sound (step4RawSources i) (step4RawSources_exact i)
        (step4OwnKeys (step4RawSourceAngle i)) point
        (step4_source_points_checked i (step4PointGroup geometric)) q hq block
    have neighbor_checked : CommonPoint.check (step4RawNeighbors j)
        (step4OwnKeys j) point = true := by
      simpa only [neighbor_equal] using step4_neighbor_points_checked geometric 0
    have neighbor_inside := (step4Neighbors j).point_sound (step4RawNeighbors j)
      (step4RawNeighbors_exact j) (step4OwnKeys j) point neighbor_checked t ht neighbor_block
    exact ⟨point.value.1, point.value.2, source_inside, neighbor_inside⟩

theorem pairStep4_geometric_sound (q t : OpenSquare)
    (hq : OrientedPoseCovered continuousScout898Domain6_4 q)
    (ht : OrientedPoseCovered continuousScout898Domain10_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout898Domain6_5 q := by
  have hp := step_sound_of_overlap continuousScout898Domain6_4Ids continuousScout898Domain10_0Ids
    step4Pieces step4Plans complement step4Sources step4Neighbors
    step4_cover step4_plans_checked step4_source_matches
    step4_neighbor_complete step4_common_overlap q t hq ht disjoint
  obtain ⟨piece, member, realizes⟩ := hp
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, _, hs, ht⟩ := step4_links_checked piece in_pieces
  refine ⟨poses (C898CompactRelaxation.links i).target, List.mem_map.mpr ⟨_, ht, rfl⟩, ?_⟩
  exact C898CompactRelaxation.link_sound i q (by simpa only [hs] using realizes)

#print axioms step4_common_overlap
#print axioms pairStep4_geometric_sound

end
end N12Compact.C898Cached.AllPairs
