import Compact.Geometry.WallInwardCenter
import Compact.Bridge.C977OppositeWallCenters
import Completion.Cases.C977.BorderPoints

/-! The two opposite wall owners cannot both own their inward extra point.
The resulting collision excludes one complete C977 vector, uniformly over
the canonical root. Every center bound is derived from actual point facts. -/
namespace N12Compact.C977OppositeWallExtras
open S12 S12Pilot S12Completion.C977 C977WallCenters C977OppositeWallCenters
set_option Elab.async false

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) (n : Nat)
    (h : ∀ owned ∈ pruningDomain4 i, n ∈ owned) :
    n ∈ natCombinedOwners p (orderedOwner p i) :=
  h _ (pruned_auxiliary_domain_actual p hf i)

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (hij : i ≠ j) : orderedOwner p i ≠ orderedOwner p j :=
  fun h => hij (ordered_owner_injective p hf h)

private theorem right_box (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 16 ∈ natCombinedOwners p (orderedOwner p 10)) :
    9/4 ≤ centerX (p.square (orderedOwner p 10)) ∧
      centerX (p.square (orderedOwner p 10)) ≤ 59/20 ∧
      9/4 ≤ centerY (p.square (orderedOwner p 10)) ∧
      centerY (p.square (orderedOwner p 10)) ≤ 59/20 := by
  have markers := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at markers
  have hP : (p.square (orderedOwner p 10)).Inside (1543/500) 2 := by
    have hp := (markers 14).mpr (by decide)
    simpa [Owns,marker] using hp
  have hQ : (p.square (orderedOwner p 10)).Inside 3 (12/5) := by
    have hp := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr
      (forced_auxiliary p hf 10 19 (by decide))
    simpa [auxPoints,fPoints,gPoints] using hp
  have hD : (p.square (orderedOwner p 10)).Inside (113/50) 2 := by
    have hp := (nat_combined_exact p (orderedOwner p 10) 16 (by decide)).mpr extra
    simpa [auxPoints,fPoints,gPoints] using hp
  have foreign : (p.square (orderedOwner p 6)).Inside 3 (87/50) := by
    have hp := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr
      (forced_auxiliary p hf 6 8 (by decide))
    simpa [auxPoints,fPoints,gPoints] using hp
  have hW : ¬ (p.square (orderedOwner p 10)).Inside 3 (87/50) :=
    fun hp => p.disjoint _ _ (apart p hf 10 6 (by decide)) _ _ ⟨hp,foreign⟩
  have hT : ¬ (p.square (orderedOwner p 10)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 10)
  have rP : (pullX (p.square (orderedOwner p 10))).Inside (457/500) 2 := by
    rw [inside_pullX]; norm_num only; exact hP
  have rQ : (pullX (p.square (orderedOwner p 10))).Inside 1 (12/5) := by
    rw [inside_pullX]; norm_num only; exact hQ
  have rD : (pullX (p.square (orderedOwner p 10))).Inside (87/50) 2 := by
    rw [inside_pullX]; norm_num only; exact hD
  have rW : ¬ (pullX (p.square (orderedOwner p 10))).Inside 1 (87/50) := by
    rw [inside_pullX]; norm_num only; exact hW
  have rT : ¬ (pullX (p.square (orderedOwner p 10))).Inside (33/20) (47/20) := by
    rw [inside_pullX]; norm_num only; exact hT
  have bound := WallInwardCenter.center_box _
    (by change 1 < (p.square (orderedOwner p 10)).side
        rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square (orderedOwner p 10)).side ≤ 1001/1000
        rw [p.congruent]; exact p.side_le)
    rP rQ rD rW rT
  simp only [center_pullX_x,center_pullX_y] at bound
  exact ⟨by linarith only [bound.2.1],by linarith only [bound.1],bound.2.2⟩

private theorem top_box (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (extra : 5 ∈ natCombinedOwners p (orderedOwner p 11)) :
    9/4 ≤ centerX (p.square (orderedOwner p 11)) ∧
      centerX (p.square (orderedOwner p 11)) ≤ 59/20 ∧
      9/4 ≤ centerY (p.square (orderedOwner p 11)) ∧
      centerY (p.square (orderedOwner p 11)) ≤ 59/20 := by
  have markers := coded_exact p (orderedOwner p 11)
  rw [ordered_owner_code p hf 11] at markers
  have hP : (p.square (orderedOwner p 11)).Inside 2 (1543/500) := by
    have hp := (markers 15).mpr (by decide)
    simpa [Owns,marker] using hp
  have hQ : (p.square (orderedOwner p 11)).Inside (12/5) 3 := by
    have hp := (nat_combined_exact p (orderedOwner p 11) 7 (by decide)).mpr
      (forced_auxiliary p hf 11 7 (by decide))
    simpa [auxPoints,fPoints,gPoints] using hp
  have hD : (p.square (orderedOwner p 11)).Inside 2 (113/50) := by
    have hp := (nat_combined_exact p (orderedOwner p 11) 5 (by decide)).mpr extra
    simpa [auxPoints,fPoints,gPoints] using hp
  have foreign : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have hp := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr
      (forced_auxiliary p hf 7 14 (by decide))
    simpa [auxPoints,fPoints,gPoints] using hp
  have hW : ¬ (p.square (orderedOwner p 11)).Inside (87/50) 3 :=
    fun hp => p.disjoint _ _ (apart p hf 11 7 (by decide)) _ _ ⟨hp,foreign⟩
  have hT : ¬ (p.square (orderedOwner p 11)).Inside (47/20) (47/20) := by
    simpa [Owns,marker] using unused_marker_ten p hf (orderedOwner p 11)
  have rP : (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside (457/500) 2 := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hP
  have rQ : (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside 1 (12/5) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hQ
  have rD : (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside (87/50) 2 := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hD
  have rW : ¬ (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside 1 (87/50) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hW
  have rT : ¬ (pullX (pullSwap (p.square (orderedOwner p 11)))).Inside (33/20) (47/20) := by
    rw [inside_pullX,inside_pullSwap]; norm_num only; exact hT
  have bound := WallInwardCenter.center_box _
    (by change 1 < (p.square (orderedOwner p 11)).side
        rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square (orderedOwner p 11)).side ≤ 1001/1000
        rw [p.congruent]; exact p.side_le)
    rP rQ rD rW rT
  simp only [center_pullX_x,center_pullX_y,center_pullSwap_x,center_pullSwap_y] at bound
  exact ⟨bound.2.2.1,bound.2.2.2,
    by linarith only [bound.2.1],by linarith only [bound.1]⟩

/-- A genuine original-family contradiction. Both wall centers would lie
in a square of side 7/10, whose squared diameter is 49/50 < 1. -/
theorem simultaneous_extras_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family)
    (rightExtra : 16 ∈ natCombinedOwners p (orderedOwner p 10))
    (topExtra : 5 ∈ natCombinedOwners p (orderedOwner p 11)) : False := by
  obtain ⟨xr0,xr1,yr0,yr1⟩ := right_box p hf rightExtra
  obtain ⟨xt0,xt1,yt0,yt1⟩ := top_box p hf topExtra
  have px := mul_nonneg
    (show 0 ≤ 7/10-(centerX (p.square (orderedOwner p 11))-
        centerX (p.square (orderedOwner p 10))) by linarith only [xt1,xr0])
    (show 0 ≤ 7/10+(centerX (p.square (orderedOwner p 11))-
        centerX (p.square (orderedOwner p 10))) by linarith only [xt0,xr1])
  have py := mul_nonneg
    (show 0 ≤ 7/10-(centerY (p.square (orderedOwner p 11))-
        centerY (p.square (orderedOwner p 10))) by linarith only [yt1,yr0])
    (show 0 ≤ 7/10+(centerY (p.square (orderedOwner p 11))-
        centerY (p.square (orderedOwner p 10))) by linarith only [yt0,yr1])
  have distance := border_packing_center_distance p
    (orderedOwner p 10) (orderedOwner p 11) (apart p hf 10 11 (by decide))
  nlinarith only [px,py,distance]

def excludedVector : List (Finset Nat) :=
  [{2,12},{0,10},∅,∅,∅,{4,13},{8,18},{3,14},{1,11},{6,15},{9,16,19},{5,7,17}]

theorem excluded_vector_present : excludedVector ∈ auxiliaryVectors := by decide

theorem extra_pair_vector_unique : ∀ v ∈ auxiliaryVectors,
    16 ∈ v[10]! → 5 ∈ v[11]! → v = excludedVector := by decide

theorem actual_not_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : actualAuxiliaryVector p ≠ excludedVector := by
  intro he
  apply simultaneous_extras_impossible p hf
  · rw [← actual_auxiliary_slot p 10,he]
    decide
  · rw [← actual_auxiliary_slot p 11,he]
    decide

def remainingVectors : List (List (Finset Nat)) :=
  auxiliaryVectors.filter fun v => decide (v ≠ excludedVector)

theorem remaining_vector_count : remainingVectors.length = 56 := by decide

/-- Original coverage now has one wall branch and 56 complete vectors.
The other 56 universal contradictions remain mathematical obligations. -/
theorem canonical_remaining_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q,
        WallHalfSpaces q w (expandWallBranch (false,false)) ∧
        actualAuxiliaryVector q ∈ remainingVectors := by
  obtain ⟨q,hframe,hq,hm,hbounds,w,v,hb,hv⟩ := canonical_single_wall_context_cover p hf
  refine ⟨q,hframe,hq,hm,hbounds,w,hb,?_⟩
  exact List.mem_filter.mpr ⟨actual_auxiliary_vector_mem q hq,
    decide_eq_true (actual_not_excluded q hq)⟩

#print axioms simultaneous_extras_impossible
#print axioms actual_not_excluded
#print axioms canonical_remaining_cover
end N12Compact.C977OppositeWallExtras
