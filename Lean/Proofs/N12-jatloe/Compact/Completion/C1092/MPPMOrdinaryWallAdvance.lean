import Compact.Completion.OtherCases.OrdinaryCentralReduction
import Compact.Completion.C1092.MPPMOmissions
import Compact.Geometry.WallLowerReach

/-! `C1092-MPPM-NONORDINARY-ISOLATION.md`, section 5.
An ordinary central point first removes the adjacent actual wall's inward
auxiliary by the whole-bar obstruction. The all-orientation wall-reach
theorem then produces a strict far point in that same actual wall.
The actual ownership of an omitted auxiliary is never reassigned.
This source has not been compiled or replayed. -/
namespace N12Compact.C1092MPPMOrdinaryWallAdvance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MPPMEntrance C1092MPPMOmissions
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem left_far (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (leftG : (owners p 8).Inside 1 (12/5))
    (bottomF : (owners p 9).Inside (8/5) 1)
    (centralF0 : (owners p 4).Inside 1 (87/50)) :
    (owners p 8).Inside 1 (64/25) := by
  have missing := Completion.OtherCases.OrdinaryCentralReduction.left_inner_absent
    p hf hb bottomF centralF0
  have mark : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  exact WallLowerReach.point (owners p 8) (side_gt p 8) (p.contained _)
    mark leftG
    (fun own => owners_disjoint p hf 8 4 (by decide) _ _ ⟨own,centralF0⟩) missing

theorem bottom_far (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (rightG : (owners p 10).Inside 3 (8/5))
    (centralG5 : (owners p 5).Inside (113/50) 1) :
    (owners p 9).Inside (36/25) 1 := by
  have missing := Completion.OtherCases.OrdinaryCentralReduction.bottom_inner_absent
    p hf hb rightG centralG5
  have mark : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  let B := pullSwap (pullX (owners p 9))
  have actual (x y : ℝ) : B.Inside x y ↔ (owners p 9).Inside (4-y) x := by
    dsimp only [B]
    rw [inside_pullSwap,inside_pullX]
  have point := WallLowerReach.point B (side_gt p 9)
    (container_pullSwap _ (container_pullX _ (p.contained _)))
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact bottomF)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 9 5 (by decide) _ _ ⟨h,centralG5⟩)
    (by intro own; have h := (actual _ _).mp own; norm_num at h; exact missing h)
  have result := (actual _ _).mp point
  norm_num at result
  exact result

theorem right_far (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (rightG : (owners p 10).Inside 3 (8/5))
    (topF : (owners p 11).Inside (12/5) 3)
    (centralF9 : (owners p 6).Inside 3 (113/50)) :
    (owners p 10).Inside 3 (36/25) := by
  have missing := Completion.OtherCases.OrdinaryCentralReduction.right_inner_absent
    p hf hb topF centralF9
  have mark : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  let B := pullY (pullX (owners p 10))
  have actual (x y : ℝ) : B.Inside x y ↔ (owners p 10).Inside (4-x) (4-y) := by
    dsimp only [B]
    rw [inside_pullY,inside_pullX]
  have point := WallLowerReach.point B (side_gt p 10)
    (container_pullY _ (container_pullX _ (p.contained _)))
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact rightG)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 10 6 (by decide) _ _ ⟨h,centralF9⟩)
    (by intro own; have h := (actual _ _).mp own; norm_num at h; exact missing h)
  have result := (actual _ _).mp point
  norm_num at result
  exact result

theorem top_far (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (topF : (owners p 11).Inside (12/5) 3)
    (leftG : (owners p 8).Inside 1 (12/5))
    (centralG4 : (owners p 7).Inside (87/50) 3) :
    (owners p 11).Inside (64/25) 3 := by
  have missing := Completion.OtherCases.OrdinaryCentralReduction.top_inner_absent
    p hf hb leftG centralG4
  have mark : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  let B := pullSwap (pullY (owners p 11))
  have actual (x y : ℝ) : B.Inside x y ↔ (owners p 11).Inside y (4-x) := by
    dsimp only [B]
    rw [inside_pullSwap,inside_pullY]
  have point := WallLowerReach.point B (side_gt p 11)
    (container_pullSwap _ (container_pullY _ (p.contained _)))
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact topF)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 11 7 (by decide) _ _ ⟨h,centralG4⟩)
    (by intro own; have h := (actual _ _).mp own; norm_num at h; exact missing h)
  have result := (actual _ _).mp point
  norm_num at result
  exact result

/-- In the no-omission branch every required ordinary wall anchor is
already strict in its original owner. Only the indicated ordinary
central point is needed to force each advance. -/
theorem bottom_far_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralG5 : (owners p 5).Inside (113/50) 1) :
    (owners p 9).Inside (36/25) 1 := by
  have walls := ordinary_walls p hb empty
  exact bottom_far p hf hb walls.2.1.1 walls.2.2.1.2 centralG5

theorem left_far_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralF0 : (owners p 4).Inside 1 (87/50)) :
    (owners p 8).Inside 1 (64/25) := by
  have walls := ordinary_walls p hb empty
  exact left_far p hf hb walls.1.2 walls.2.1.1 centralF0

theorem right_far_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralF9 : (owners p 6).Inside 3 (113/50)) :
    (owners p 10).Inside 3 (36/25) := by
  have walls := ordinary_walls p hb empty
  exact right_far p hf hb walls.2.2.1.2 walls.2.2.2.1 centralF9

theorem top_far_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralG4 : (owners p 7).Inside (87/50) 3) :
    (owners p 11).Inside (64/25) 3 := by
  have walls := ordinary_walls p hb empty
  exact top_far p hf hb walls.2.2.2.1 walls.1.2 centralG4

theorem all_far_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralF0 : (owners p 4).Inside 1 (87/50))
    (centralG5 : (owners p 5).Inside (113/50) 1)
    (centralF9 : (owners p 6).Inside 3 (113/50))
    (centralG4 : (owners p 7).Inside (87/50) 3) :
    (owners p 8).Inside 1 (64/25) ∧ (owners p 9).Inside (36/25) 1 ∧
      (owners p 10).Inside 3 (36/25) ∧ (owners p 11).Inside (64/25) 3 :=
  ⟨left_far_no_omission p hf hb empty centralF0,
    bottom_far_no_omission p hf hb empty centralG5,
    right_far_no_omission p hf hb empty centralF9,
    top_far_no_omission p hf hb empty centralG4⟩

/-- Every point of this whole foreign bar stays in the one actual Q9.
The endpoints may subsequently be used separately, but no interval
between different foreign owners has been introduced. -/
theorem bottom_bar_no_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (centralG5 : (owners p 5).Inside (113/50) 1)
    (x : ℝ) (low : 36/25≤x) (high : x≤87/50) :
    (owners p 9).Inside x 1 :=
  CommonCases.OriginalOwners.horizontal_segment (owners p 9) (36/25) (87/50) 1 x
    (bottom_far_no_omission p hf hb empty centralG5) (wall_auxiliaries p hb).2.1
    (by norm_num) low high

#print axioms left_far
#print axioms bottom_far
#print axioms right_far
#print axioms top_far
#print axioms all_far_no_omission
#print axioms bottom_bar_no_omission
end N12Compact.C1092MPPMOrdinaryWallAdvance
