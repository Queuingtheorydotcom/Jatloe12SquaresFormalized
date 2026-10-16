import Compact.Completion.C1092.MPPMActualRightNear
import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNortheast
import Compact.Completion.C1092.MMMP.TwoFifthsEntranceFloor

/-! Actual MPPM one-omission E/N/R inputs for the common two-fifths
ending. In the common transposed chart these are original Q7/Q6/Q11.
The actual bottom bar belongs to original Q8. Neither G8 alternative is
discarded, and no angle bound from its omitted alternative is transferred
to its owned alternative. The northeast upper-third bound is separate.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualProfiles
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MMMPEndingAxes C1092MMMPTwoFifthsEntrance
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

theorem northeast_core (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (N : OpenSquare) (np : C1092MPPMUpperSign.PositiveActual p N) : NortheastCore N := by
  have m : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using mark p hf 6 10 (by decide +kernel)
  have k : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have core := C1092MPPMPointCore.rectangle p hf hb omitted
  have pair := (omitted_bottom_neighbors p hf hb omitted).1
  apply northeast_faces N (by rw [np.side]; exact side_gt p 6)
    (by linarith only [(normal_bounds np.normal).1]) np.positive np.normal.2.1
  · apply (np.actual _ _).mpr; norm_num; exact m
  · apply (np.actual _ _).mpr; norm_num; exact pair.1
  · apply (np.actual _ _).mpr; norm_num; exact pair.2
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨original,core _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨original,core _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨original,C1092MPPMTopOrigin.right_origin p hf hb omitted⟩
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨original,k⟩
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 11 (by decide) _ _
      ⟨original,(wall_auxiliaries p hb).2.2.2⟩
  · intro own
    have original := (np.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 6 11 (by decide) _ _
      ⟨original,(C1092MPPMRightInner.other_ordinary p hf hb omitted).2⟩

structure SoutheastActual (p : NormalizedPacking) (E : OpenSquare) : Prop where
  side : E.side=(owners p 7).side
  actual : ∀ x y,E.Inside x y↔(owners p 7).Inside (2+y) (2+x)
  normal : Normal E.c E.s
  positive : 0<E.s

theorem southeast_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3)
    (N : OpenSquare) (np : C1092MPPMUpperSign.PositiveActual p N) :
    ∃ E : OpenSquare,SoutheastActual p E ∧ C1092TwoFifths.Southeast E ∧
      E.loU+E.side≤E.c-(13/50)*E.s := by
  obtain ⟨C,cp⟩ := C1092MPPMActualRightNear.exists_positive p hf hb omitted near
  let E := clockwise (clockwise (clockwise C))
  have eActual (x y : ℝ) : E.Inside x y↔(owners p 7).Inside (2+y) (2+x) := by
    simp only [E,inside_clockwise,neg_neg]
    rw [cp.actual]
    simp only [sub_neg_eq_add]
  have ep : SoutheastActual p E := ⟨cp.side,eActual,cp.normal,cp.positive⟩
  have side : 1<E.side := by rw [ep.side]; exact side_gt p 7
  have cosine : 0<E.c := by linarith only [(normal_bounds ep.normal).1]
  have sine : 0<E.s := ep.positive
  have order : E.s≤E.c := ep.normal.2.1
  have pair := C1092MPPMActualRightNear.inward_pair p hf hb omitted near
  have m : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using mark p hf 7 11 (by decide +kernel)
  have marker : E.Inside (7/20) (-7/20) := by apply (ep.actual _ _).mpr; norm_num; exact m
  have inner : E.Inside 0 (-13/50) := by apply (ep.actual _ _).mpr; norm_num; exact pair.2
  have forward : E.Inside (13/50) 0 := by apply (ep.actual _ _).mpr; norm_num; exact pair.1
  have noOrigin : ¬E.Inside 0 0 := by
    intro own
    have original := (ep.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 7 5 (by decide) _ _
      ⟨original,C1092MPPMOmissionCenter.bottom_center p hf hb omitted⟩
  have noNear : ¬E.Inside 1 (-13/50) := by
    intro own
    have original := (ep.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 7 11 (by decide) _ _ ⟨original,near⟩
  have noSharp : ¬E.Inside (47/100) (3/25) := by
    intro own
    exact owners_disjoint p hf 7 6 (by decide) _ _
      ⟨(ep.actual _ _).mp own,(np.actual _ _).mp (northeast_core p hf hb omitted N np).sharp⟩
  have caps := southeast_caps E side cosine sine order marker inner forward noOrigin noNear
  let B := (pullSwap (owners p 8)).translated 2 2
  have bActual (x y : ℝ) : B.Inside x y↔(owners p 8).Inside (2+y) (2+x) := by
    dsimp only [B]
    rw [inside_translated_iff,inside_pullSwap]
  have bar (x : ℝ) (low : 0≤x) (high : x≤2/5) : B.Inside x (-1) := by
    apply (bActual _ _).mpr
    norm_num
    exact CommonCases.OriginalOwners.vertical_segment _ _ _ _ _
      (C1092MPPMActualRightNear.left_origin p hf hb omitted near)
      (C1092MPPMRightInner.other_ordinary p hf hb omitted).1
      (by norm_num) (by linarith only [low]) (by linarith only [high])
  have apart : ∀ x y,¬(E.Inside x y ∧ B.Inside x y) := fun x y both =>
    owners_disjoint p hf 7 8 (by decide) _ _
      ⟨(ep.actual _ _).mp both.1,(bActual _ _).mp both.2⟩
  refine ⟨E,ep,?_,caps.2⟩
  by_cases outer : (owners p 7).Inside (8/5) 3
  · have outerE : E.Inside 1 (-2/5) := by apply (ep.actual _ _).mpr; norm_num; exact outer
    have sharp := southeast_outer_cap E cosine sine order inner forward outerE noSharp
    have floor := southeast_floor E B side cosine sine order sharp.2
      marker inner forward caps.1 caps.2 bar apart
    exact ⟨side,cosine,sine,southeast_outer_small E side cosine sine order caps.2 sharp.1 floor,
      inner,forward,caps.1,floor⟩
  · have small := C1092MMMPPositiveInwardHalfangle.small_angle_of_bar C
      (by rw [cp.side]; exact side_gt p 7) cp.normal
      (by apply (cp.actual _ _).mpr; norm_num; exact m)
      (by apply (cp.actual _ _).mpr; norm_num; exact pair.1)
      (by apply (cp.actual _ _).mpr; norm_num; exact pair.2)
      (by
        intro own
        have original := (cp.actual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 7 5 (by decide) _ _
          ⟨original,C1092MPPMOmissionCenter.bottom_center p hf hb omitted⟩)
      (by
        intro own
        have original := (cp.actual _ _).mp own
        norm_num at original
        exact outer original)
      (by
        intro y low high own
        have original := (cp.actual _ _).mp own
        norm_num at original
        have foreign : (owners p 8).Inside 1 (2+y) :=
          CommonCases.OriginalOwners.vertical_segment _ _ _ _ _
            (C1092MPPMActualRightNear.left_origin p hf hb omitted near)
            (C1092MPPMRightInner.other_ordinary p hf hb omitted).1
            (by norm_num) (by linarith only [low]) (by linarith only [high])
        exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨original,foreign⟩)
    have smallE : E.s<21/100 := small.2.1
    have closeE : 97/100<E.c := small.2.2
    have floor := southeast_floor E B side cosine sine order
      (by linarith only [smallE]) marker inner forward caps.1 caps.2 bar apart
    exact ⟨side,cosine,sine,by linarith only [smallE,closeE],inner,forward,caps.1,floor⟩

/-- R is literally original Q11 in the common transposed coordinates.
Its complete strict short bar and center sign are derived together. -/
theorem right_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3) :
    C1092TwoFifths.Right ((pullSwap (owners p 11)).translated 2 2) := by
  let R := (pullSwap (owners p 11)).translated 2 2
  have actual (x y : ℝ) : R.Inside x y↔(owners p 11).Inside (2+y) (2+x) := by
    dsimp only [R]
    rw [inside_translated_iff,inside_pullSwap]
  refine ⟨?_,?_,?_⟩
  · intro y low high
    apply (actual _ _).mpr
    norm_num
    exact CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ near
      (C1092MPPMRightInner.other_ordinary p hf hb omitted).2
      (by norm_num) (by linarith only [low]) (by linarith only [high])
  · intro x y own
    have wall := (p.contained _ _ _ ((actual _ _).mp own)).2.2.2
    linarith only [wall]
  · have center : centerY R=centerX (owners p 11)-2 := by
      dsimp [R,OpenSquare.translated,pullSwap,centerY,centerX]
      linear_combination -2*(owners p 11).unit_normal
    rw [center]
    have cut : 2≤centerX (owners p 11) := by
      simpa [mppm,wallFrame,localFrame,wallOwner] using (hb 3).1
    linarith only [cut]

end
#print axioms northeast_core
#print axioms southeast_profile
#print axioms right_profile
end N12Compact.C1092MPPMActualProfiles
