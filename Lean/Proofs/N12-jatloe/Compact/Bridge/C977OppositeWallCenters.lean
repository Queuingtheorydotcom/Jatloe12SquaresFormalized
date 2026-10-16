import Compact.Geometry.WallLowerCenterBarrier
import Compact.Bridge.C977WallCenters

/-! Both opposite-wall centers lie above their midpoint splits, uniformly
over all 57 actual ownership vectors. Combined with the previous two wall
cuts, only the all-upper wall branch survives. No whole vector is excluded. -/
namespace N12Compact.C977OppositeWallCenters
open S12 S12Pilot S12Completion S12Completion.C977 C977WallCenters
set_option Elab.async false

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (n : Nat)
    (h : ∀ owned ∈ pruningDomain4 i, n ∈ owned) :
    n ∈ natCombinedOwners p (orderedOwner p i) :=
  h _ (pruned_auxiliary_domain_actual p hf i)

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (hij : i ≠ j) : orderedOwner p i ≠ orderedOwner p j :=
  fun h => hij (ordered_owner_injective p hf h)

/-- The right center is above 2.1. The lower foreign point belongs to
owner6 in every vector; marker10 is globally unused in the original family. -/
theorem right_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    21/10 < centerY (p.square (orderedOwner p 10)) := by
  have markers := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at markers
  have hP : (p.square (orderedOwner p 10)).Inside (1543/500) 2 := by
    have hp := (markers 14).mpr (by decide)
    simpa [Owns, marker] using hp
  have hQ : (p.square (orderedOwner p 10)).Inside 3 (12/5) := by
    have owned := forced_auxiliary p hf 10 19 (by decide)
    have hp := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints, fPoints, gPoints] using hp
  have foreign : (p.square (orderedOwner p 6)).Inside 3 (87/50) := by
    have owned := forced_auxiliary p hf 6 8 (by decide)
    have hp := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints, fPoints, gPoints] using hp
  have hW : ¬ (p.square (orderedOwner p 10)).Inside 3 (87/50) :=
    fun hp => p.disjoint _ _ (apart p hf 10 6 (by decide)) _ _ ⟨hp,foreign⟩
  have hT : ¬ (p.square (orderedOwner p 10)).Inside (47/20) (47/20) := by
    simpa [Owns, marker] using unused_marker_ten p hf (orderedOwner p 10)
  have rP : (pullX (p.square (orderedOwner p 10))).Inside (457/500) 2 := by
    rw [inside_pullX]
    norm_num only
    exact hP
  have rQ : (pullX (p.square (orderedOwner p 10))).Inside 1 (12/5) := by
    rw [inside_pullX]
    norm_num only
    exact hQ
  have rW : ¬ (pullX (p.square (orderedOwner p 10))).Inside 1 (87/50) := by
    rw [inside_pullX]
    norm_num only
    exact hW
  have rT : ¬ (pullX (p.square (orderedOwner p 10))).Inside (33/20) (47/20) := by
    rw [inside_pullX]
    norm_num only
    exact hT
  have high := WallLowerCenterBarrier.center_above _
    (by change 1 < (p.square (orderedOwner p 10)).side
        rw [p.congruent]; exact p.side_gt_one)
    (container_pullX _ (p.contained _)) rP rQ rW rT
  simpa only [center_pullX_y] using high

/-- The top-owner version transports only this geometric lemma; the actual
packing and its canonical missing-corner frame are left unchanged. -/
theorem top_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    21/10 < centerX (p.square (orderedOwner p 11)) := by
  have markers := coded_exact p (orderedOwner p 11)
  rw [ordered_owner_code p hf 11] at markers
  have hP : (p.square (orderedOwner p 11)).Inside 2 (1543/500) := by
    have hp := (markers 15).mpr (by decide)
    simpa [Owns, marker] using hp
  have hQ : (p.square (orderedOwner p 11)).Inside (12/5) 3 := by
    have owned := forced_auxiliary p hf 11 7 (by decide)
    have hp := (nat_combined_exact p (orderedOwner p 11) 7 (by decide)).mpr owned
    simpa [auxPoints, fPoints, gPoints] using hp
  have foreign : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have owned := forced_auxiliary p hf 7 14 (by decide)
    have hp := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr owned
    simpa [auxPoints, fPoints, gPoints] using hp
  have hW : ¬ (p.square (orderedOwner p 11)).Inside (87/50) 3 :=
    fun hp => p.disjoint _ _ (apart p hf 11 7 (by decide)) _ _ ⟨hp,foreign⟩
  have hT : ¬ (p.square (orderedOwner p 11)).Inside (47/20) (47/20) := by
    simpa [Owns, marker] using unused_marker_ten p hf (orderedOwner p 11)
  have rP : (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside (457/500) 2 := by
    rw [inside_pullX, inside_pullSwap]
    norm_num only
    exact hP
  have rQ : (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside 1 (12/5) := by
    rw [inside_pullX, inside_pullSwap]
    norm_num only
    exact hQ
  have rW : ¬ (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside 1 (87/50) := by
    rw [inside_pullX, inside_pullSwap]
    norm_num only
    exact hW
  have rT : ¬ (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside (33/20) (47/20) := by
    rw [inside_pullX, inside_pullSwap]
    norm_num only
    exact hT
  have high := WallLowerCenterBarrier.center_above _
    (by change 1 < (p.square (orderedOwner p 11)).side
        rw [p.congruent]; exact p.side_gt_one)
    (container_pullX _ (container_pullSwap _ (p.contained _))) rP rQ rW rT
  simpa only [center_pullX_y, center_pullSwap_y] using high

/-- Both remaining lower-half decisions contradict original geometry.
Equality at either midpoint is included, and no ownership vector is dropped. -/
theorem opposite_branch_restriction (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family)
    (w : WallOwners p) (b : OppositeWallBranch)
    (hb : WallHalfSpaces p w (expandWallBranch b)) :
    b = (false,false) := by
  have hi2 : w.index 2 = orderedOwner p 10 := by
    apply markerCode_injective p
    rw [w.code, ordered_owner_code p hf]
    rfl
  have hi3 : w.index 3 = orderedOwner p 11 := by
    apply markerCode_injective p
    rw [w.code, ordered_owner_code p hf]
    rfl
  have first : b.1 = false := by
    cases h : b.1 with
    | false => rfl
    | true =>
      have low := hb 2
      change (if b.1 then centerY (p.square (w.index 2)) ≤ 2 else
        2 ≤ centerY (p.square (w.index 2))) at low
      rw [h, hi2] at low
      simp only [ite_true] at low
      have high := right_center p hf
      exfalso
      linarith only [low,high]
  have second : b.2 = false := by
    cases h : b.2 with
    | false => rfl
    | true =>
      have low := hb 3
      change (if b.2 then centerX (p.square (w.index 3)) ≤ 2 else
        2 ≤ centerX (p.square (w.index 3))) at low
      rw [h, hi3] at low
      simp only [ite_true] at low
      have high := top_center p hf
      exfalso
      linarith only [low,high]
  exact Prod.ext first second

/-- Whole-packing coverage with just the all-upper wall branch and all 57
actual vectors. The original canonical missing-corner facts persist. -/
theorem canonical_single_wall_context_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q, ∃ v : Fin auxiliaryVectors.length,
        WallHalfSpaces q w (expandWallBranch (false,false)) ∧
        auxiliaryVectors.get v = actualAuxiliaryVector q := by
  obtain ⟨q,hframe,hq,hm,hbounds,w,c,hb,hv⟩ := canonical_four_wall_context_cover p hf
  have restriction := opposite_branch_restriction q hq w c.1 hb
  rw [restriction] at hb
  exact ⟨q,hframe,hq,hm,hbounds,w,c.2,hb,hv⟩

/-- The remaining case theorem requires 57 complete geometric exclusions.
The uniform wall cuts are a reduction, not any one of those exclusions. -/
theorem excludes_case_of_single_wall_contexts
    (hcontext : ∀ (p : NormalizedPacking),
      codedMarkerFamily p = family →
      StrengthenedMissingCorner (p.square (orderedOwner p 0)) →
      CanonicalCornerBounds (p.square (orderedOwner p 0)) →
      ∀ (w : WallOwners p) (v : Fin auxiliaryVectors.length),
        WallHalfSpaces p w (expandWallBranch (false,false)) →
        auxiliaryVectors.get v = actualAuxiliaryVector p → False) : ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q,_,hq,hm,hbounds,w,v,hb,hv⟩ := canonical_single_wall_context_cover p hf
  exact hcontext q hq hm hbounds w v hb hv

#print axioms right_center
#print axioms top_center
#print axioms canonical_single_wall_context_cover
end N12Compact.C977OppositeWallCenters
