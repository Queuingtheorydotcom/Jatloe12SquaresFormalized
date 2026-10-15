import Compact.Cases.C713.HeightData.All
import Compact.Cases.C713.SharedDomains
import Compact.Cases.C713.OccupiedRow

/-! Replace the original C713 chord stage by the original owner's occupied
row bound. Every original incoming pose is covered by an exact height record;
empty outputs are disproved by that record, and surviving outputs retain the
original pose and its angle. No propagated neighbor cover is assumed. -/

namespace N12Compact.C713ChordDirect
open S12 S12Pilot C713Shared C713Height C713HeightData
set_option Elab.async false

theorem source_to_after_height (p : NormalizedPacking)
    (family : codedMarkerFamily p = case713Family)
    (incoming : OrientedPoseCovered continuousScout713Domain7_0
      (p.square (ownerIndex p 2304))) :
    OrientedPoseCovered continuousScout713Domain7_6
      (p.square (ownerIndex p 2304)) := by
  obtain ⟨leaf,leaf_mem,realized⟩ := incoming
  obtain ⟨source,source_mem,rfl⟩ := List.mem_map.mp leaf_mem
  have member : source ∈ (List.finRange 108).map
      (fun i => (record i).spec.source) := by
    rw [source_ids]
    exact source_mem
  obtain ⟨i,i_mem,source_eq⟩ := List.mem_map.mp member
  have realized' : (poses (record i).spec.source).OrientedRealizes
      (p.square (ownerIndex p 2304)) := by
    simpa only [source_eq] using realized
  have checked := record_checked i
  have height := C713OccupiedRow.above_radius p family
    (poses (record i).spec.source) (record i).radius checked.2.1 realized'.2
  have cut := (record i).cut_holds checked _ height
  have outgoing := (record i).spec.sound dictionary
    HistoricalData.positive_denominators checked.1
    (p.square (ownerIndex p 2304)) realized' (p.contained _) cut
  obtain ⟨leaf,leaf_mem,realized⟩ := outgoing
  obtain ⟨target,target_mem,rfl⟩ := List.mem_map.mp leaf_mem
  refine ⟨poses target, List.mem_map.mpr ⟨target,?_,rfl⟩, realized⟩
  rw [← target_ids]
  exact List.mem_flatMap.mpr ⟨i,i_mem,target_mem⟩

#print axioms source_to_after_height
end N12Compact.C713ChordDirect
