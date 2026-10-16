import Compact.Completion.C1092.MMMP.PointCore
import Compact.Completion.C1092.MMMP.OuterArm
import Compact.Completion.CommonCases.InwardPoint

/-! The actual northwest excludes the outer left auxiliary, before any
left-wall G1 or top-origin conclusion. The strict second inward tip then
follows from the unchanged all-angle inward-square theorem. -/
namespace N12Compact.C1092MMMPInwardTips
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore
set_option Elab.async false

theorem missing_outer (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : ¬(owners p 7).Inside 1 (12/5) := by
  intro outer
  let C := (pullX (owners p 7)).translated 2 2
  let W := (pullX (owners p 8)).translated 2 2
  have nw := northwest_pair p hf hb
  have markC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markW : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have markN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markD : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  apply C1092MMMPOuterArm.impossible C W (side_gt p 7) (side_same p 7 8)
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact northwest_center p hf hb
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact markC
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact nw.1
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact nw.2
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact outer
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact fun own => owners_disjoint p hf 7 11 (by decide) _ _ ⟨own,(top_pair p hf hb).1⟩
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact fun own => owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,markN⟩
  · norm_num [C,inside_translated_iff,inside_pullX]
    exact fun own => owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,markD⟩
  · norm_num [W,inside_translated_iff,inside_pullX]
    exact markW
  · norm_num [W,inside_translated_iff,inside_pullX]
    exact (wall_auxiliaries p hb).1
  · intro x y own
    have h := (inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own)
    have box := p.contained _ _ _ h
    linarith only [box.1]
  · have cut : 2≤centerY (owners p 8) := by
      simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 0).1
    have center : centerY W=centerY (owners p 8)-2 := by
      dsimp [W,OpenSquare.translated,pullX,centerY]
      linear_combination -2*(owners p 8).unit_normal
    rw [center]
    linarith only [cut]
  · intro x y own
    exact owners_disjoint p hf 7 8 (by decide) _ _
      ⟨(inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own.1),
        (inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own.2)⟩

theorem second_tip (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside (199/100) (127/50) := by
  have nw := northwest_pair p hf hb
  have markC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markD : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have answer := CommonCases.InwardPoint.strong_original (pullSwap (owners p 7)) (side_gt p 7)
    (by norm_num [inside_pullSwap]; exact markC)
    (by norm_num [inside_pullSwap]; exact nw.2)
    (by norm_num [inside_pullSwap]; exact nw.1)
    (by
      norm_num [inside_pullSwap]
      exact fun own => owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,markD⟩)
    (by
      norm_num [inside_pullSwap]
      exact fun own => owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,markN⟩)
    (by norm_num [inside_pullSwap]; exact missing_outer p hf hb)
  norm_num [inside_pullSwap] at answer
  exact answer

#print axioms missing_outer
#print axioms second_tip
end N12Compact.C1092MMMPInwardTips
