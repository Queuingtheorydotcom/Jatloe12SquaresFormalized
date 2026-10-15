import Compact.Completion.C1092.MMMP.NortheastActualSign
import Compact.Completion.C1092.MMMP.RightInnerPositive
import Compact.Completion.C1092.MMMP.RightNearAdvance

/-! Original MMMP right-inner exclusion. All auxiliary covers concern the
actual original owners. A direct near-point advance replaces the combined
component enumeration used in the prose reference. -/
namespace N12Compact.C1092MMMPRightInnerActual
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092AuxiliaryCover C1092MMMPNortheastActualSign
set_option Elab.async false

theorem southeast_pair_of_inner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (inner : (owners p 10).Inside (113/50) 2) :
    (owners p 5).Inside 3 (87/50) ∧ (owners p 5).Inside 3 (8/5) := by
  classical
  have bottom := (wall_auxiliaries p hb).2.1
  have g : (owners p 5).Inside 3 (8/5) := by
    rcases southeast_g_cover p hf with h|h|h
    · exact False.elim (owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom⟩)
    · exact False.elim (owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,inner⟩)
    · exact h
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have bottomTip : (owners p 9).Inside (239/100) 1 := by
    have h := local_wall_segment p mmmp hb 1 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have mark : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have f : (owners p 5).Inside 3 (87/50) := by
    by_contra absent
    have noOuter : ¬(owners p 5).Inside (12/5) 1 := by
      intro outer
      apply C1092CornerTwoGaps.impossible (pullY (owners p 5)) (side_gt p 5)
        (39/100) (13/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · norm_num [inside_pullY]; exact mark
      · norm_num [inside_pullY]; exact outer
      · norm_num [inside_pullY]; exact g
      · norm_num [inside_pullY]
        exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bottomTip⟩
      · norm_num [inside_pullY]; exact absent
      · norm_num [inside_pullY]
        exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,corner⟩
    rcases C1092MMMMEntrance.southeast_f_cover p hf with h|h|h
    · exact C1092MixedSpan.impossible (owners p 5) (side_gt p 5) h g
        (fun own => owners_disjoint p hf 5 10 (by decide) _ _ ⟨own,inner⟩) absent
        (fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bottom⟩) noOuter
    · exact noOuter h
    · exact absent h
  exact ⟨f,g⟩

theorem right_missing_inner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : ¬(owners p 10).Inside (113/50) 2 := by
  intro inner
  have se := (southeast_pair_of_inner p hf hb inner).1
  have ne := northeast_pair p hf hb
  have markerR : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have markerN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have tip : (owners p 10).Inside 3 (239/100) := by
    have h := local_wall_segment p mmmp hb 2 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  let R := (owners p 10).translated 2 2
  have rMissing : ¬R.Inside 1 (-13/50) := by
    norm_num [R,inside_translated_iff]
    exact fun own => owners_disjoint p hf 10 5 (by decide) _ _ ⟨own,se⟩
  have rMarkerMissing : ¬R.Inside (7/20) (7/20) := by
    norm_num [R,inside_translated_iff]
    exact fun own => owners_disjoint p hf 10 6 (by decide) _ _ ⟨own,markerN⟩
  have upper := C1092MMMPRightNearAdvance.point R (side_gt p 10)
    (by norm_num [R,inside_translated_iff]; exact inner)
    (by norm_num [R,inside_translated_iff]; exact markerR)
    (by norm_num [R,inside_translated_iff]; exact tip) rMissing rMarkerMissing
  obtain ⟨N,np⟩ := exists_positive p hf hb
  apply C1092MMMPRightInnerPositive.impossible N R
    (by rw [np.side]; exact side_gt p 6) (np.side.trans (side_same p 6 10)) np.normal
  · apply (np.actual _ _).mpr
    norm_num
    exact markerN
  · apply (np.actual _ _).mpr
    norm_num
    exact ne.2
  · apply (np.actual _ _).mpr
    norm_num
    exact ne.1
  · norm_num [R,inside_translated_iff]
    exact inner
  · norm_num [R,inside_translated_iff]
    exact markerR
  · exact upper
  · exact rMissing
  · intro x y own
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨(np.actual _ _).mp own.1,(inside_translated_iff _ _ _ _ _).mp own.2⟩

#print axioms southeast_pair_of_inner
#print axioms right_missing_inner
end N12Compact.C1092MMMPRightInnerActual
