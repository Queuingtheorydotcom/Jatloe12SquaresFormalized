import Compact.Completion.C1092.MPPMUpperOrigin
import Compact.Completion.C1092.MMMP.StrongNortheastFaces
import Compact.Geometry.WallUpperMissingReach

/-! The sole ordinary-right alternative in the actual MPPM one-omission
branch. The common chart is the transpose about (2,2): W is actual Q5,
N is actual Q6, and the right bar is in actual Q11. Omitting transposed
F8 means omitting original G4 in that Q11. The original mixed Q9 supplies
the separate left gap. The full all-sign MMMP local ending is reused only
after its entire actual input is derived; no MMMP wall context is assumed.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualOneOmission
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092RigidCharts
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

/-- The entire right bar in the common transposed chart has the one
original owner Q11. Its origin was proved before this extra-point split. -/
theorem top_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 11).Inside (87/50) 3) :
    (owners p 11).Inside (64/25) 3 ∧
      ∀ x : ℝ,2≤x → x≤64/25 → (owners p 11).Inside x 3 := by
  let R := pullSwap (pullY (owners p 11))
  have markerR : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using mark p hf 11 15 (by decide +kernel)
  have markerN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using mark p hf 6 10 (by decide +kernel)
  have far := WallUpperMissingReach.point R (side_gt p 11)
    (container_pullSwap _ (container_pullY _ (p.contained _)))
    (by norm_num [R,inside_pullSwap,inside_pullY]; exact markerR)
    (by norm_num [R,inside_pullSwap,inside_pullY]
      exact (C1092MPPMRightInner.other_ordinary p hf hb omitted).2)
    (by norm_num [R,inside_pullSwap,inside_pullY]; exact missing)
    (by norm_num [R,inside_pullSwap,inside_pullY]
      exact fun own => owners_disjoint p hf 11 6 (by decide) _ _ ⟨own,markerN⟩)
  have actual : (owners p 11).Inside (64/25) 3 := by
    norm_num [R,inside_pullSwap,inside_pullY] at far
    exact far
  exact ⟨actual,fun x low high => CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _
    (C1092MPPMUpperOrigin.top_origin p hf hb omitted) actual (by norm_num) low high⟩

/-- The genuine N profile and strict steep-angle bound. No northeast
face, side upper bound or desired support is assumed by this adapter. -/
theorem northeast_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 11).Inside (87/50) 3)
    (N : OpenSquare) (np : C1092MPPMUpperSign.PositiveActual p N) :
    C1092MMMPEnding.Profile N ∧ 252/373≤N.s := by
  have markerN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using mark p hf 6 10 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have rectangle := C1092MPPMPointCore.rectangle p hf hb omitted
  have ordinary := (omitted_bottom_neighbors p hf hb omitted).1
  apply C1092MMMPStrongNortheastFaces.profile N
    (by rw [np.side]; exact side_gt p 6) np.normal
  · apply (np.actual _ _).mpr; norm_num; exact markerN
  · apply (np.actual _ _).mpr; norm_num; exact ordinary.1
  · intro own
    have actual := (np.actual _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨actual,rectangle _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · intro own
    have actual := (np.actual _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨actual,rectangle _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  · intro own
    have actual := (np.actual _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨actual,C1092MPPMTopOrigin.right_origin p hf hb omitted⟩
  · intro own
    have actual := (np.actual _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨actual,corner⟩
  · intro y low high own
    have actual := (np.actual _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 6 11 (by decide) _ _
      ⟨actual,(top_reach p hf hb omitted missing).2 _ (by linarith only [low])
        (by linarith only [high])⟩

theorem impossible_of_top_g4_omission (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (omitted : ¬(owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 11).Inside (87/50) 3) : False := by
  obtain ⟨N,np⟩ := C1092MPPMUpperSign.exists_positive p hf hb omitted
  have profile := northeast_profile p hf hb omitted missing N np
  let W := translate (pullSwap (owners p 5)) 2 2
  have actualW (x y : ℝ) : W.Inside x y↔(owners p 5).Inside (2+y) (2+x) := by
    rw [W,inside_translate,inside_pullSwap]
    rw [show y+2=2+y by ring,show x+2=2+x by ring]
  have mW : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have mS : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  have mN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using mark p hf 6 10 (by decide +kernel)
  apply C1092MMMPEnding.impossible W N (side_gt p 5)
    ((side_same p 5 6).trans np.side.symm) np.normal profile.2 profile.1
  · apply (actualW _ _).mpr; norm_num
    exact C1092MPPMOmissionCenter.bottom_center p hf hb omitted
  · apply (actualW _ _).mpr; norm_num
    exact C1092MPPMPointCore.bottom_crosspoint p hf hb omitted
  · apply (actualW _ _).mpr; norm_num
    exact (C1092MPPMPointCore.diagonal p hf hb omitted).1
  · apply (actualW _ _).mpr; norm_num; exact mW
  · intro own
    have actual := (actualW _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨actual,mS⟩
  · intro own
    have actual := (actualW _ _).mp own
    norm_num at actual
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨actual,omitted_bottom_bar p hf hb omitted _ (by norm_num) (by norm_num)⟩
  · apply (np.actual _ _).mpr; norm_num; exact mN
  · apply (np.actual _ _).mpr; norm_num
    exact (omitted_bottom_neighbors p hf hb omitted).1.1
  · apply (np.actual _ _).mpr; norm_num
    exact (omitted_bottom_neighbors p hf hb omitted).1.2
  · intro x y both
    exact owners_disjoint p hf 5 6 (by decide) _ _
      ⟨(actualW _ _).mp both.1,(np.actual _ _).mp both.2⟩

/-- The only still-untranslated one-omission entrance is the actual
right-near branch: original Q11 must own G4=(1.74,3). This is a proved
point consequence, not a complete single-omission exclusion. -/
theorem top_g4 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 11).Inside (87/50) 3 := by
  by_contra missing
  exact impossible_of_top_g4_omission p hf hb omitted missing

end
#print axioms impossible_of_top_g4_omission
#print axioms top_g4
end N12Compact.C1092MPPMActualOneOmission
