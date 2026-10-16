import Compact.Completion.C1092.MPPMOrdinaryCycleData
import Compact.Completion.C1092.MPPMFourCycleStates

/-! Complete ordinary windmill ending. The five finite sign schemas
use only the continuous original-owner rules in OrdinaryCycleData.
Canonical frame selection preserves each actual square and every strict
membership; a zero angle is included in the nonpositive branch.
Source only, without compiler or replay acceptance. -/
namespace N12Compact.C1092MPPMOrdinaryCycle
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
open C1092MPPMActualPositiveCycle C1092MPPMActualCrosspoints
set_option Elab.async false
noncomputable section

theorem one_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p)
    (positive : Positive d 0) (n1 : ¬Positive d 1)
    (n2 : ¬Positive d 2) (n3 : ¬Positive d 3) : False := by
  classical
  have edge := signed_edge p hf hb h d 3 n3 (by simpa [addSector] using positive)
  have r3 : Retains p 3 := edge.1
  have m0 : ¬Retains p 0 := by simpa [addSector] using edge.2
  by_cases r1 : Retains p 1
  · by_cases r2 : Retains p 2
    · exact three_retaining p hf hb h d 1 n1
        (by simpa [addSector] using n2) (by simpa [addSector] using n3)
        r1 (by simpa [addSector] using r2) (by simpa [addSector] using r3)
    · exact missing_before_positive p hf hb h d 3
        (by simpa [addSector] using n2) (by simpa [addSector] using r2) n3 r3
        (by simpa [addSector] using positive) (by simpa [addSector] using m0)
  · by_cases r2 : Retains p 2
    · exact missing_before_retaining p hf hb h d 2
        (by simpa [addSector] using n1) (by simpa [addSector] using r1) n2 r2
        (by simpa [addSector] using n3) (by simpa [addSector] using r3)
        (by simpa [addSector] using positive)
    · exact adjacent_missing p hf hb h d 1 n1 (by simpa [addSector] using n2)
        r1 (by simpa [addSector] using r2)

theorem sandwich (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p)
    (p0 : Positive d 0) (n1 : ¬Positive d 1) (p2 : Positive d 2) : False := by
  have edge := signed_edge p hf hb h d 1 n1 (by simpa [addSector] using p2)
  exact positive_sandwich p hf hb h d 1 (by simpa [addSector] using p0) n1
    (by simpa [addSector] using p2) edge.1 edge.2

theorem adjacent_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p)
    (p0 : Positive d 0) (p1 : Positive d 1)
    (n2 : ¬Positive d 2) (n3 : ¬Positive d 3) : False := by
  classical
  have edge := signed_edge p hf hb h d 3 n3 (by simpa [addSector] using p0)
  have r3 : Retains p 3 := edge.1
  have m0 : ¬Retains p 0 := by simpa [addSector] using edge.2
  by_cases r2 : Retains p 2
  · exact positive_before_retaining p hf hb h d 2 (by simpa [addSector] using p1)
      n2 r2 (by simpa [addSector] using n3) (by simpa [addSector] using r3)
      (by simpa [addSector] using p0)
  · exact missing_before_positive p hf hb h d 3
      (by simpa [addSector] using n2) (by simpa [addSector] using r2) n3 r3
      (by simpa [addSector] using p0) (by simpa [addSector] using m0)

/-- The genuine Ordinary entrance is the only geometric entrance
premise. The actual positive crosspoints, wall profiles, origins, whole
foreign bars, angle ceilings and same-wall center orders are all proved
upstream. No finite component receipt or pose table is used here. -/
theorem impossible_of_frames (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (d : Frames p) : False := by
  have zero (i : Fin 4) : addSector i 0=i := by fin_cases i <;> rfl
  rcases C1092MPPMFourCycle.classify (Positive d) with nonpositive|positive|one|mixed|adjacent
  · exact C1092MPPMAllNonpositive.impossible p hf hb h d.square d.frame
      (fun i => d.nonpositive_normal i (nonpositive i))
  · exact C1092MPPMActualPositiveCycle.impossible p hf hb h
      (fun i => ⟨d.square i,d.frame i,d.positive_normal i (positive i),positive i⟩)
  · obtain ⟨i,one⟩ := one
    let d' := d.rotated hf i
    apply one_positive ((rotation i).pullPacking p) (family_transport (rotation i) p hf)
      (rotation_context p hf hb i) (Ordinary.rotated p hf h i) d'
    · change Positive d (addSector i 0)
      simpa only [zero] using one.1
    · exact one.2.1
    · exact one.2.2.1
    · exact one.2.2.2
  · obtain ⟨i,mixed⟩ := mixed
    let d' := d.rotated hf i
    apply sandwich ((rotation i).pullPacking p) (family_transport (rotation i) p hf)
      (rotation_context p hf hb i) (Ordinary.rotated p hf h i) d'
    · change Positive d (addSector i 0)
      simpa only [zero] using mixed.1
    · exact mixed.2.1
    · exact mixed.2.2
  · obtain ⟨i,adjacent⟩ := adjacent
    let d' := d.rotated hf i
    apply adjacent_positive ((rotation i).pullPacking p) (family_transport (rotation i) p hf)
      (rotation_context p hf hb i) (Ordinary.rotated p hf h i) d'
    · change Positive d (addSector i 0)
      simpa only [zero] using adjacent.1
    · exact adjacent.2.1
    · exact adjacent.2.2.1
    · exact adjacent.2.2.2

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) : False := by
  obtain ⟨d⟩ := Frames.exists p
  exact impossible_of_frames p hf hb h d

end
#print axioms impossible_of_frames
#print axioms impossible
end N12Compact.C1092MPPMOrdinaryCycle
