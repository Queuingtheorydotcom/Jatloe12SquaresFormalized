import Compact.Completion.C1092.MPPMActualOneOmission
import Compact.Completion.C1092.MMMP.ShortBarNegative
import Compact.Completion.C1092.MMMP.InwardOuterArmHalfpoint

/-! The actual right-near entrance in the normalized MPPM one-omission
branch. Transposed right-near F8 is original Q11's G4. It forces original
Q7's inward pair, its genuine positive inward frame, and original Q8's
origin. Both outer-point alternatives use the same actual Q8 bar and
actual paired Q3. No MMMP context or sign of the mixed Q9 is substituted.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualRightNear
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem inward_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3) :
    (owners p 7).Inside 2 (113/50) ∧ (owners p 7).Inside (87/50) 2 := by
  have lF := (wall_auxiliaries p hb).1
  have lG := (C1092MPPMRightInner.other_ordinary p hf hb omitted).1
  have g3 : (owners p 7).Inside (87/50) 2 := by
    rcases C1092AuxiliaryCover.northwest_g_cover p hf with own | own | own
    · exact False.elim (owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,lG⟩)
    · exact own
    · exact False.elim (owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,near⟩)
  refine ⟨?_,g3⟩
  by_contra missing
  have f3 : (owners p 7).Inside (8/5) 3 := by
    rcases C1092AuxiliaryCover.northwest_f_cover p hf with own | own | own
    · exact False.elim (owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,lF⟩)
    · exact own
    · exact False.elim (missing own)
  exact C1092MixedSpan.impossible (pullSwap (owners p 7)) (side_gt p 7)
    (by norm_num [inside_pullSwap]; exact g3)
    (by norm_num [inside_pullSwap]; exact f3)
    (by norm_num [inside_pullSwap]; exact missing)
    (by norm_num [inside_pullSwap]; exact fun own =>
      owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,near⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,lF⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,lG⟩)

structure PositiveInward (p : NormalizedPacking) (C : OpenSquare) : Prop where
  side : C.side=(owners p 7).side
  actual : ∀ x y,C.Inside x y↔(owners p 7).Inside (2-x) (2+y)
  normal : Normal C.c C.s
  positive : 0<C.s

/-- The same short bar in original Q11, between its proved origin and
the presently owned G4, excludes every nonpositive canonical frame. -/
theorem exists_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3) :
    ∃ C : OpenSquare,PositiveInward p C := by
  let A := (pullX (owners p 7)).translated 2 2
  obtain ⟨C,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame A
  have actual (x y : ℝ) : C.Inside x y↔(owners p 7).Inside (2-x) (2+y) := by
    rw [inside]
    dsimp only [A]
    rw [inside_translated_iff,inside_pullX]
    rw [show (4:ℝ)-(2+x)=2-x by ring]
  have pair := inward_pair p hf hb omitted near
  have mC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using mark p hf 7 11 (by decide +kernel)
  have mW : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have walls := wall_auxiliaries p hb
  have lG := (C1092MPPMRightInner.other_ordinary p hf hb omitted).1
  let W := (pullX (owners p 8)).translated 2 2
  have wActual (x y : ℝ) : W.Inside x y↔(owners p 8).Inside (2-x) (2+y) := by
    dsimp only [W]
    rw [inside_translated_iff,inside_pullX]
    rw [show (4:ℝ)-(2+x)=2-x by ring]
  have tip : (owners p 8).Inside 1 (239/100) := by
    have point := local_wall_segment p mppm hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mppm,wallOwner,pointMap,branchY] at point
    exact point
  have positive : 0<C.s := by
    apply lt_of_not_ge
    intro nonpositive
    have cn : Normal C.c (-C.s) := ⟨by linarith only [nonpositive],
      by simpa only [abs_of_nonpos nonpositive] using canonical,
      by nlinarith only [C.unit_normal]⟩
    apply C1092MMMPShortBarNegative.impossible C W cn
      (by rw [shape]; exact side_gt p 7) (shape.trans (side_same p 7 8))
    · apply (actual _ _).mpr; norm_num; exact mC
    · apply (actual _ _).mpr; norm_num; exact pair.1
    · apply (actual _ _).mpr; norm_num; exact pair.2
    · intro own
      have original := (actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 7 5 (by decide) _ _
        ⟨original,C1092MPPMOmissionCenter.bottom_center p hf hb omitted⟩
    · intro own
      have original := (actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨original,lG⟩
    · intro own
      have original := (actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨original,near⟩
    · intro x low high own
      have original := (actual _ _).mp own
      norm_num at original
      have foreign : (owners p 11).Inside (2-x) 3 :=
        CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ near
          (C1092MPPMUpperOrigin.top_origin p hf hb omitted) (by norm_num)
          (by linarith only [high]) (by linarith only [low])
      exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨original,foreign⟩
    · apply (wActual _ _).mpr; norm_num; exact mW
    · apply (wActual _ _).mpr; norm_num; exact walls.1
    · apply (wActual _ _).mpr; norm_num; exact tip
    · intro x y own
      have wall := (p.contained _ _ _ ((wActual _ _).mp own)).1
      linarith only [wall]
    · have center : centerY W=centerY (owners p 8)-2 := by
        dsimp [W,OpenSquare.translated,pullX,centerY]
        linear_combination -2*(owners p 8).unit_normal
      rw [center]
      have cut : 2≤centerY (owners p 8) := by
        simpa [mppm,wallFrame,localFrame,wallOwner] using (hb 0).1
      linarith only [cut]
    · intro x y both
      exact owners_disjoint p hf 7 8 (by decide) _ _
        ⟨(actual _ _).mp both.1,(wActual _ _).mp both.2⟩
  exact ⟨C,shape,actual,⟨positive.le,
    by simpa only [abs_of_pos positive] using canonical,C.unit_normal⟩,positive⟩

/-- Both original corner walls are retained in the contraposition. -/
theorem corner_halfpoint_of_missing_left_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (leftG : (owners p 8).Inside 1 (12/5))
    (missing : ¬(owners p 8).Inside 1 2) : (owners p 3).Inside (3/2) 3 := by
  classical
  by_contra half
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have km : (owners p 3).Inside (457/500) 3 := by
    simpa [marker] using mark p hf 3 7 (by decide +kernel)
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  let B := pullX (pullSwap (owners p 8))
  let K := pullX (pullSwap (owners p 3))
  have boxB := container_pullX (pullSwap (owners p 8))
    (container_pullSwap (owners p 8) (p.contained _))
  have boxK := container_pullX (pullSwap (owners p 3))
    (container_pullSwap (owners p 3) (p.contained _))
  have origin := Completion.OtherCases.WallProfile.boundary_origin B K (457/500) (8/5)
    (side_gt p 8) (side_same p 8 3)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [B,inside_pullX,inside_pullSwap]; exact lm)
    (by norm_num [B,inside_pullX,inside_pullSwap]; exact leftG)
    (by norm_num [K,inside_pullX,inside_pullSwap]; exact km)
    (by norm_num [K,inside_pullX,inside_pullSwap]; exact corner)
    (by norm_num [K,inside_pullX,inside_pullSwap]; exact half)
    (fun x y both => owners_disjoint p hf 3 8 (by decide) _ _
      ⟨(inside_pullSwap _ _ _).mp ((inside_pullX _ _ _).mp both.1),
        (inside_pullSwap _ _ _).mp ((inside_pullX _ _ _).mp both.2)⟩)
  apply missing
  norm_num [B,inside_pullX,inside_pullSwap] at origin
  exact origin

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3) : (owners p 8).Inside 1 2 := by
  classical
  obtain ⟨C,cp⟩ := exists_positive p hf hb omitted near
  have pair := inward_pair p hf hb omitted near
  have lF := (wall_auxiliaries p hb).1
  have lG := (C1092MPPMRightInner.other_ordinary p hf hb omitted).1
  have mC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using mark p hf 7 11 (by decide +kernel)
  have mW : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have m : C.Inside (7/20) (7/20) := by apply (cp.actual _ _).mpr; norm_num; exact mC
  have i : C.Inside 0 (13/50) := by apply (cp.actual _ _).mpr; norm_num; exact pair.1
  have j : C.Inside (13/50) 0 := by apply (cp.actual _ _).mpr; norm_num; exact pair.2
  have o : ¬C.Inside 0 0 := by
    intro own
    have original := (cp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 7 5 (by decide) _ _
      ⟨original,C1092MPPMOmissionCenter.bottom_center p hf hb omitted⟩
  by_contra missing
  have half := corner_halfpoint_of_missing_left_origin p hf lG missing
  have outerMissing : ¬C.Inside (1/2) 1 := by
    intro own
    have original := (cp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 7 3 (by decide) _ _ ⟨original,half⟩
  by_cases outer : (owners p 7).Inside (8/5) 3
  · apply outerMissing
    apply C1092MMMPInwardOuterArmHalfpoint.point C
      (by rw [cp.side]; exact side_gt p 7) m i j
    · apply (cp.actual _ _).mpr; norm_num; exact outer
    · exact o
    · intro own
      have original := (cp.actual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨original,near⟩
    · intro y low high own
      have original := (cp.actual _ _).mp own
      norm_num at original
      have foreign : (owners p 8).Inside 1 (2+y) :=
        CommonCases.OriginalOwners.vertical_segment _ _ _ _ _ lF lG
          (by norm_num) (by linarith only [low]) (by linarith only [high])
      exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨original,foreign⟩
  · let W := (pullX (owners p 8)).translated 2 2
    have actualW (x y : ℝ) : W.Inside x y↔(owners p 8).Inside (2-x) (2+y) := by
      dsimp only [W]
      rw [inside_translated_iff,inside_pullX]
      rw [show (4:ℝ)-(2+x)=2-x by ring]
    apply C1092MMMPBottomOriginObstruction.impossible C W
      (by rw [cp.side]; exact side_gt p 7) (cp.side.trans (side_same p 7 8)) cp.normal m i j o
    · intro own
      have original := (cp.actual _ _).mp own
      norm_num at original
      exact outer original
    · exact outerMissing
    · apply (actualW _ _).mpr; norm_num; exact mW
    · apply (actualW _ _).mpr; norm_num; exact lF
    · apply (actualW _ _).mpr; norm_num; exact lG
    · intro own
      have original := (actualW _ _).mp own
      norm_num at original
      exact missing original
    · intro x y own
      have wall := (p.contained _ _ _ ((actualW _ _).mp own)).1
      linarith only [wall]
    · intro x y both
      exact owners_disjoint p hf 7 8 (by decide) _ _
        ⟨(cp.actual _ _).mp both.1,(actualW _ _).mp both.2⟩

end
#print axioms inward_pair
#print axioms exists_positive
#print axioms left_origin
end N12Compact.C1092MPPMActualRightNear
