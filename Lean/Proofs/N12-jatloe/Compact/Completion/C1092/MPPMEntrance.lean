import Compact.Completion.C1092.MMMMEntrance
import Compact.Completion.CommonCases.OriginalOwners

/-! Original MPPM wall-omission ancestry. Only genuine single-cover
consequences, the six-point obstruction, and actual disjointness are used.
The conclusion retains the original owner of every strict point. -/
namespace N12Compact.C1092MPPMEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092AuxiliaryCover
set_option Elab.async false

def mppm : WallBranch := ![false,true,true,false]

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem wall_auxiliaries (p : NormalizedPacking) (hb : WallContext p mppm) :
    (owners p 8).Inside 1 (113/50) ∧
    (owners p 9).Inside (87/50) 1 ∧
    (owners p 10).Inside 3 (87/50) ∧
    (owners p 11).Inside (113/50) 3 := by
  have h0 := wall_auxiliary_point p mppm hb 0
  have h1 := wall_auxiliary_point p mppm hb 1
  have h2 := wall_auxiliary_point p mppm hb 2
  have h3 := wall_auxiliary_point p mppm hb 3
  norm_num [mppm,wallOwner,pointMap,branchY] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

/-- An omitted ordinary bottom auxiliary extends this same bottom owner
past both inward auxiliary abscissae. No combined-label list is assumed. -/
theorem omitted_bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬ (owners p 9).Inside (8/5) 1) :
    ∀ x : ℝ, 161/100 ≤ x → x ≤ 12/5 → (owners p 9).Inside x 1 := by
  have wall := (wall_auxiliaries p hb).2.1
  have marker : (owners p 9).Inside 2 (457/500) := by
    have h : Owns (owners p 9) 13 := (owners_markers p hf 9 13).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have forward : (owners p 9).Inside (12/5) 1 := by
    have h := wall_cover_transported ⟨true,false,false⟩ p hf
    norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
    rcases h with h | h | h
    · exact False.elim (omitted h)
    · exact h
    · have six := side_six_point (pullSwap (owners p 9)) (side_gt p 9)
        ((inside_pullSwap _ _ _).mpr marker)
        ((inside_pullSwap _ _ _).mpr wall)
        ((inside_pullSwap _ _ _).mpr h)
      norm_num [inside_pullSwap] at six
      rcases six with low | high | foreign
      · exact False.elim (omitted low)
      · exact high
      · exact False.elim (owners_disjoint p hf 9 4 (by decide) _ _
          ⟨foreign,C1092ActualEntrance.southwest_marker p hf⟩)
  have low : (owners p 9).Inside (161/100) 1 := by
    have h := local_wall_segment p mppm hb 1 (161/100) (by norm_num) (by norm_num)
    norm_num [mppm,wallOwner,pointMap,branchY] at h
    exact h
  intro x hx hy
  exact CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ low forward
    (by norm_num) hx hy

theorem omitted_bottom_inward (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (omitted : ¬ (owners p 9).Inside (8/5) 1) :
    (owners p 5).Inside 2 (87/50) ∧ (owners p 5).Inside (113/50) 2 := by
  classical
  have bar := omitted_bottom_bar p hf hb omitted
  have bottomF : (owners p 9).Inside (12/5) 1 := bar _ (by norm_num) (by norm_num)
  have bottomG : (owners p 9).Inside (113/50) 1 := bar _ (by norm_num) (by norm_num)
  have right := (wall_auxiliaries p hb).2.2.1
  have inward : (owners p 5).Inside 2 (87/50) := by
    rcases C1092MMMMEntrance.southeast_f_cover p hf with h | h | h
    · exact h
    · exact False.elim (owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottomF⟩)
    · exact False.elim (owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,right⟩)
  have cross : (owners p 5).Inside (113/50) 2 := by
    by_contra absent
    have outer : (owners p 5).Inside 3 (8/5) := by
      rcases southeast_g_cover p hf with h | h | h
      · exact False.elim (owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottomG⟩)
      · exact False.elim (absent h)
      · exact h
    exact C1092MixedSpan.impossible (owners p 5) (side_gt p 5) inward outer absent
      (fun h => owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,right⟩)
      (fun h => owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottomG⟩)
      (fun h => owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottomF⟩)
  exact ⟨inward,cross⟩

/-- The neighboring northeast ordinary pair and actual right ordinary
pair are forced before any center or crosspoint theorem is invoked. -/
theorem omitted_bottom_neighbors (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (omitted : ¬ (owners p 9).Inside (8/5) 1) :
    ((owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)) ∧
    ((owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5)) := by
  classical
  have inward := omitted_bottom_inward p hf hb omitted
  have wall := wall_auxiliaries p hb
  have northeastG : (owners p 6).Inside 3 (12/5) := by
    rcases northeast_g_cover p hf with h | h | h
    · exact False.elim (owners_disjoint p hf 6 5 (by decide) _ _ ⟨h,inward.2⟩)
    · exact False.elim (owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,wall.2.2.2⟩)
    · exact h
  have rightG : (owners p 10).Inside 3 (8/5) := by
    rcases right_g_cover p hf with h | h | h
    · exact False.elim (owners_disjoint p hf 10 5 (by decide) _ _ ⟨h,inward.2⟩)
    · exact h
    · exact False.elim (owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,northeastG⟩)
  have topTip : (owners p 11).Inside (239/100) 3 := by
    have h := local_wall_segment p mppm hb 3 (161/100) (by norm_num) (by norm_num)
    norm_num [mppm,wallOwner,pointMap,branchY] at h
    exact h
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have marker : (owners p 6).Inside (47/20) (47/20) := by
    have h : Owns (owners p 6) 10 := (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have northeastF : (owners p 6).Inside 3 (113/50) := by
    by_contra absent
    have noTop : ¬ (owners p 6).Inside (12/5) 3 := by
      intro outer
      exact C1092CornerTwoGaps.impossible (owners p 6) (side_gt p 6)
        (39/100) (13/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        marker outer northeastG
        (fun h => owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,by norm_num; exact topTip⟩)
        (by norm_num; exact absent)
        (fun h => owners_disjoint p hf 6 2 (by decide) _ _ ⟨h,corner⟩)
    rcases northeast_f_cover p hf with h | h | h
    · apply C1092MixedSpan.impossible (pullY (owners p 6)) (side_gt p 6)
      · norm_num [inside_pullY]; exact h
      · norm_num [inside_pullY]; exact northeastG
      · norm_num [inside_pullY]
        exact fun h => owners_disjoint p hf 6 5 (by decide) _ _ ⟨h,inward.2⟩
      · norm_num [inside_pullY]; exact absent
      · norm_num [inside_pullY]
        exact fun h => owners_disjoint p hf 6 11 (by decide) _ _ ⟨h,wall.2.2.2⟩
      · norm_num [inside_pullY]; exact noTop
    · exact noTop h
    · exact absent h
  exact ⟨⟨northeastF,northeastG⟩,⟨wall.2.2.1,rightG⟩⟩

#print axioms omitted_bottom_neighbors
end N12Compact.C1092MPPMEntrance
