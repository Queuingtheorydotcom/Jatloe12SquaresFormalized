import Compact.Completion.C1092.MMMP.BottomOriginEntrance
import Compact.Completion.C1092.MMMP.BottomOriginObstruction

/-! Actual-owner conclusions of DOUBLE-RIGHT-BOTTOM-ORIGIN sections 4--5,
also giving the outer-point-exclusion alternative in RIGHT-NEAR-BOTTOM-ORIGIN.
The right-near premise and southeast outer-point exclusion remain explicit;
the bottom-origin conclusion itself has no additional support assumption. -/
namespace N12Compact.C1092MMMPBottomOrigin
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

/-- A genuine right near point forces the bottom origin whenever the
actual southeast square omits its outer right point. -/
theorem point_of_near (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (outerMissing : ¬(owners p 5).Inside 3 (8/5)) :
    (owners p 9).Inside 2 1 := by
  classical
  by_contra missing
  obtain ⟨C,actual⟩ := C1092MMMPSoutheastSign.exists_positive p hf hb near
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have corner := C1092MMMPBottomOriginEntrance.corner_halfpoint p hf hb missing
  have markC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have markW : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  let W := (pullSwap (pullY (owners p 9))).translated 2 2
  have wallInside (x y : ℝ) : W.Inside x y ↔ (owners p 9).Inside (2+y) (2-x) := by
    simp only [W,inside_translated_iff,inside_pullSwap,inside_pullY]
    rw [show 4-(2+x)=2-x by ring]
  apply C1092MMMPBottomOriginObstruction.impossible C W
    (by rw [actual.side]; exact side_gt p 5)
    (by dsimp [W]; exact actual.side.trans (side_same p 5 9)) actual.normal
  · apply (actual.actual _ _).mpr
    norm_num
    exact markC
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.2
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.1
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact outerMissing h
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨h,corner⟩
  · apply (wallInside _ _).mpr
    norm_num
    exact markW
  · apply (wallInside _ _).mpr
    norm_num
    exact bottom.2
  · apply (wallInside _ _).mpr
    norm_num
    exact bottom.1
  · intro own
    have h := (wallInside _ _).mp own
    norm_num at h
    exact missing h
  · intro x y own
    have h := (wallInside x y).mp own
    have box := p.contained _ _ _ h
    linarith only [box.2.2.1]
  · intro x y own
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨(actual.actual x y).mp own.1,(wallInside x y).mp own.2⟩

/-- The strict bottom bar gives exactly the quantitative southeast
angle bound recorded in the completed prose. -/
theorem small_angle_of_near (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (outerMissing : ¬(owners p 5).Inside 3 (8/5)) :
    ∃ C : OpenSquare, C1092MMMPSoutheastSign.PositiveActual p C ∧
      C.s+(2/5)*C.c<3/5 ∧ C.s<21/100 ∧ 97/100<C.c := by
  obtain ⟨C,actual⟩ := C1092MMMPSoutheastSign.exists_positive p hf hb near
  have origin := point_of_near p hf hb near outerMissing
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have markC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  refine ⟨C,actual,?_⟩
  apply C1092MMMPPositiveInwardHalfangle.small_angle_of_bar C
    (by rw [actual.side]; exact side_gt p 5) actual.normal
  · apply (actual.actual _ _).mpr
    norm_num
    exact markC
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.2
  · apply (actual.actual _ _).mpr
    norm_num
    exact inward.1
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩
  · intro own
    have h := (actual.actual _ _).mp own
    norm_num at h
    exact outerMissing h
  · intro y yn yu own
    have h := (actual.actual _ _).mp own
    norm_num at h
    have bar := inside_segment (owners p 9) 2 1 (12/5) 1 ((5/2)*y)
      origin bottom.1 (by nlinarith only [yn]) (by nlinarith only [yu])
    have strict : (owners p 9).Inside (2+y) 1 := by
      convert bar using 1 <;> ring
    exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,strict⟩

/-- In particular, ownership of the lower outer right point supplies all
premises of the paper's double-right bottom-origin conclusion. -/
theorem point_of_lower (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (lower : (owners p 10).Inside 3 (8/5)) : (owners p 9).Inside 2 1 := by
  have near : (owners p 10).Inside 3 (87/50) := by
    have h := inside_segment (owners p 10) 3 (8/5) 3 (113/50) (7/33)
      lower (wall_auxiliaries p hb).2.2.1 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  exact point_of_near p hf hb near
    (fun own => owners_disjoint p hf 5 10 (by decide) _ _ ⟨own,lower⟩)

#print axioms point_of_near
#print axioms small_angle_of_near
#print axioms point_of_lower
end N12Compact.C1092MMMPBottomOrigin
