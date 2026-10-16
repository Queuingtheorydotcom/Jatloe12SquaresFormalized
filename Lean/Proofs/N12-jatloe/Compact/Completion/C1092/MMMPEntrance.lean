import Compact.Completion.C1092.MMMMEntrance

/-! Universal original MMMP core ownership. The northwest inward pair follows
directly from the two physical incoming wall signs, and the remaining joins
use elementary single covers plus two genuine all-angle point obstructions. -/
namespace N12Compact.C1092MMMPEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092ActualEntrance C1092AuxiliaryCover
set_option Elab.async false

def mmmp : WallBranch := ![false,false,false,true]

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem wall_auxiliaries (p : NormalizedPacking) (hb : WallContext p mmmp) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 9).Inside (113/50) 1 ∧
      (owners p 10).Inside 3 (113/50) ∧ (owners p 11).Inside (87/50) 3 := by
  have h0 := wall_auxiliary_point p mmmp hb 0
  have h1 := wall_auxiliary_point p mmmp hb 1
  have h2 := wall_auxiliary_point p mmmp hb 2
  have h3 := wall_auxiliary_point p mmmp hb 3
  norm_num [mmmp,wallOwner,pointMap,branchY] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) :
    (owners p 7).Inside 2 (113/50) ∧ (owners p 7).Inside (87/50) 2 :=
  C1092ActualEntrance.northwest_pair p hf mmmp hb rfl rfl

theorem northeast_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 6).Inside (12/5) 3 := by
  have wall := wall_auxiliaries p hb
  have inward := northwest_pair p hf hb
  rcases northeast_f_cover p hf with h | h | h
  · exact False.elim (owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,inward.1⟩)
  · exact h
  · exact False.elim (owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,wall.2.2.1⟩)

theorem top_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) :
    (owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3 := by
  have inward := northwest_pair p hf hb
  have outer := northeast_f p hf hb
  have f : (owners p 11).Inside (8/5) 3 := by
    rcases top_f_cover p hf with h | h | h
    · exact h
    · exact False.elim (owners_disjoint p hf 11 7 (by decide) _ _ ⟨h,inward.1⟩)
    · exact False.elim (owners_disjoint p hf 11 6 (by decide) _ _ ⟨h,outer⟩)
  exact ⟨f,(wall_auxiliaries p hb).2.2.2⟩

theorem northeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) :
    (owners p 6).Inside (12/5) 3 ∧ (owners p 6).Inside (113/50) 3 := by
  classical
  have f := northeast_f p hf hb
  have inward := northwest_pair p hf hb
  have right := (wall_auxiliaries p hb).2.2.1
  have rightTip : (owners p 10).Inside 3 (239/100) := by
    have h := local_wall_segment p mmmp hb 2 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h : Owns (owners p 6) 10 := (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have g : (owners p 6).Inside (113/50) 3 := by
    by_contra absent
    have noRight : ¬ (owners p 6).Inside 3 (12/5) := by
      intro outer
      exact C1092CornerTwoGaps.impossible (owners p 6) (side_gt p 6)
        (13/50) (39/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        marker f outer (by norm_num; exact absent)
        (fun h => owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,by norm_num; exact rightTip⟩)
        (fun h => owners_disjoint p hf 6 2 (by decide) _ _ ⟨h,corner⟩)
    rcases northeast_g_cover p hf with h | h | h
    · apply C1092MixedSpan.impossible (pullSwap (pullX (owners p 6))) (side_gt p 6)
      · norm_num [inside_pullSwap,inside_pullX]; exact h
      · norm_num [inside_pullSwap,inside_pullX]; exact f
      · norm_num [inside_pullSwap,inside_pullX]
        exact fun h => owners_disjoint p hf 6 7 (by decide) _ _ ⟨h,inward.1⟩
      · norm_num [inside_pullSwap,inside_pullX]; exact absent
      · norm_num [inside_pullSwap,inside_pullX]
        exact fun h => owners_disjoint p hf 6 10 (by decide) _ _ ⟨h,right⟩
      · norm_num [inside_pullSwap,inside_pullX]; exact noRight
    · exact absent h
    · exact noRight h
  exact ⟨f,g⟩

theorem northeast_no_both (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) :
    ¬ ((owners p 6).Inside (113/50) 2 ∧ (owners p 6).Inside 3 (12/5)) := by
  intro both
  have right : (owners p 10).Inside 3 (8/5) := by
    rcases right_g_cover p hf with h | h | h
    · exact False.elim (owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,both.1⟩)
    · exact h
    · exact False.elim (owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,both.2⟩)
  rcases southeast_g_cover p hf with h | h | h
  · exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,(wall_auxiliaries p hb).2.1⟩
  · exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,both.1⟩
  · exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,right⟩

#print axioms northeast_pair
#print axioms northeast_no_both
end N12Compact.C1092MMMPEntrance
