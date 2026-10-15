import Completion.Cases.C696.AuxiliaryNecessity
import Compact.Geometry.WallLowerCenterBarrier
import Compact.Geometry.WallLowerReach

/-! Uniform consequences of the actual C696 ownership assignment.
The four wall squares are transformed individually only to apply a geometric
lemma. No independent changes to the packing or ownership are made.
Both original corner roots remain open. -/
namespace N12Compact.C696WallCycle
open S12 S12Pilot S12Completion.C696
open SideSignPacking
set_option Elab.async false

theorem owners_markers (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ExactMarkers (owners p i) (maskSupport (ownerMasks i)) := by
  have he := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  simpa only [owners,he] using coded_exact p (ownerIndex p (ownerMasks i))

theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem side_le (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side ≤ 1001/1000 := by
  change (p.square _).side ≤ 1001/1000
  rw [p.congruent]
  exact p.side_le

theorem actual_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    AuxExact (owners p i) 2 (auxiliaryVector i) := by
  simpa only [owners, AuxiliaryNecessity.exact_assignment p hf i] using
    nat_combined_exact p (ownerIndex p (ownerMasks i))

theorem inside_query (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (P : ℚ × ℚ)
    (hP : P ∈ queryInsidePoints (ownerMasks i) 2 (auxiliaryVector i)) :
    (owners p i).Inside P.1 P.2 :=
  query_inside_sound _ _ _ _ (side_gt p i) (side_le p i) (p.contained _)
    (owners_markers p hf i) (actual_auxiliary p hf i) P hP

theorem outside_query (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (P : ℚ × ℚ)
    (hP : P ∈ queryOutsidePoints (ownerMasks i) 2 (auxiliaryVector i)) :
    ¬ (owners p i).Inside P.1 P.2 :=
  query_outside_sound _ _ _ _ (owners_markers p hf i)
    (actual_auxiliary p hf i) P hP

def wallOwner : Fin 4 → Fin 12 := ![8,9,10,11]

noncomputable def wallFrame (p : NormalizedPacking) : Fin 4 → OpenSquare :=
  ![owners p 8, pullSwap (owners p 9), pullX (pullY (owners p 10)),
    pullX (pullY (pullSwap (owners p 11)))]

def wallPoint (i : Fin 4) (P : ℚ × ℚ) : ℚ × ℚ :=
  ![P, (P.2,P.1), (4-P.1,4-P.2), (4-P.2,4-P.1)] i

private theorem frame_inside (p : NormalizedPacking) (i : Fin 4) (P : ℚ × ℚ) :
    (wallFrame p i).Inside P.1 P.2 ↔
      (owners p (wallOwner i)).Inside (wallPoint i P).1 (wallPoint i P).2 := by
  fin_cases i <;>
    simp [wallFrame,wallOwner,wallPoint,inside_pullX,inside_pullY,inside_pullSwap]

private theorem frame_side (p : NormalizedPacking) (i : Fin 4) :
    1 < (wallFrame p i).side := by
  have same : (wallFrame p i).side = (owners p (wallOwner i)).side := by
    fin_cases i <;> rfl
  rw [same]
  exact side_gt p (wallOwner i)

private theorem frame_box (p : NormalizedPacking) (i : Fin 4) :
    InsideContainer (wallFrame p i) := by
  fin_cases i
  · exact p.contained _
  · exact container_pullSwap _ (p.contained _)
  · exact container_pullX _ (container_pullY _ (p.contained _))
  · exact container_pullX _ (container_pullY _ (container_pullSwap _ (p.contained _)))

private theorem frame_owned (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (P : ℚ × ℚ) (hp : ∀ i : Fin 4, wallPoint i P ∈
      queryInsidePoints (ownerMasks (wallOwner i)) 2 (auxiliaryVector (wallOwner i)))
    (i : Fin 4) : (wallFrame p i).Inside P.1 P.2 :=
  (frame_inside p i P).mpr (inside_query p hf _ _ (hp i))

private theorem frame_missing (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (P : ℚ × ℚ) (hp : ∀ i : Fin 4, wallPoint i P ∈
      queryOutsidePoints (ownerMasks (wallOwner i)) 2 (auxiliaryVector (wallOwner i)))
    (i : Fin 4) : ¬ (wallFrame p i).Inside P.1 P.2 :=
  fun hi => outside_query p hf _ _ (hp i) ((frame_inside p i P).mp hi)

/-- The same five point facts hold in every wall frame. Membership checks
only bind named original markers and auxiliary points, never pose boxes. -/
theorem frame_progress (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 4) :
    21/10 < centerY (wallFrame p i) ∧ (wallFrame p i).Inside 1 (64/25) := by
  have hP : (wallFrame p i).Inside (457/500) 2 := by
    simpa using frame_owned p hf ((457/500,2) : ℚ × ℚ)
      (by decide +kernel) i
  have hQ : (wallFrame p i).Inside 1 (12/5) := by
    simpa using frame_owned p hf ((1,12/5) : ℚ × ℚ)
      (by decide +kernel) i
  have hW : ¬ (wallFrame p i).Inside 1 (87/50) := by
    simpa using frame_missing p hf ((1,87/50) : ℚ × ℚ)
      (by decide +kernel) i
  have hD : ¬ (wallFrame p i).Inside (87/50) 2 := by
    simpa using frame_missing p hf ((87/50,2) : ℚ × ℚ)
      (by decide +kernel) i
  have hT : ¬ (wallFrame p i).Inside (33/20) (47/20) := by
    simpa using frame_missing p hf ((33/20,47/20) : ℚ × ℚ)
      (by decide +kernel) i
  exact ⟨WallLowerCenterBarrier.center_above _ (frame_side p i) (frame_box p i)
      hP hQ hW hT,
    WallLowerReach.point _ (frame_side p i) (frame_box p i) hP hQ hW hD⟩

/-- A quantitative replacement for the original four midpoint signs. -/
theorem center_cuts (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    21/10 < centerY (owners p 8) ∧ 21/10 < centerX (owners p 9) ∧
      centerY (owners p 10) < 19/10 ∧ centerX (owners p 11) < 19/10 := by
  have h0 := (frame_progress p hf 0).1
  have h1 := (frame_progress p hf 1).1
  have h2 := (frame_progress p hf 2).1
  have h3 := (frame_progress p hf 3).1
  simp [wallFrame] at h0 h1 h2 h3
  exact ⟨h0,h1,by linarith only [h2],by linarith only [h3]⟩

/-- Four strict owned points follow simultaneously from the actual family. -/
theorem owned_points (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 8).Inside 1 (64/25) ∧ (owners p 9).Inside (64/25) 1 ∧
      (owners p 10).Inside 3 (36/25) ∧ (owners p 11).Inside (36/25) 3 := by
  have h0 := (frame_progress p hf 0).2
  have h1 := (frame_progress p hf 1).2
  have h2 := (frame_progress p hf 2).2
  have h3 := (frame_progress p hf 3).2
  norm_num [wallFrame,inside_pullX,inside_pullY,inside_pullSwap] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

#print axioms frame_progress
#print axioms center_cuts
#print axioms owned_points
end N12Compact.C696WallCycle
