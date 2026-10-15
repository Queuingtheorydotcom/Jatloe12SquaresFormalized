import Compact.Completion.C1092.MMMP.Origins
import Compact.Completion.C1092.IncomingCenters
import Compact.Completion.C1092.InwardCenterDiagonal
import Compact.Completion.C1092.MMMP.CenterCrosspoint

/-! The actual NW center, left halfpoint and complete diagonal interval
needed by the shorter MMMP ending. No second center crosspoint or vacancy
assignment is used by these deductions. -/
namespace N12Compact.C1092MMMPPointCore
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
set_option Elab.async false

theorem northwest_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside 2 2 :=
  C1092IncomingCenters.northwest p hf mmmp hb rfl rfl

theorem northwest_diagonal_interval (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (k : ℝ) (lower : 7/20≤k) (length : k^2≤151/400) :
    (owners p 7).Inside (2-k) (2+k) := by
  let q := (pullX (owners p 7)).translated 2 2
  have mark : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have neMark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have swMark : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have h := C1092InwardCenterDiagonal.diagonal q (side_gt p 7)
    (by norm_num [q,inside_translated_iff,inside_pullX]; exact northwest_center p hf hb)
    (by norm_num [q,inside_translated_iff,inside_pullX]; exact mark)
    (by
      norm_num [q,inside_translated_iff,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,neMark⟩)
    (by
      norm_num [q,inside_translated_iff,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,swMark⟩)
    k lower length
  have result := (inside_translated_iff (pullX (owners p 7)) 2 2 k k).mp h
  have result' := (inside_pullX _ _ _).mp result
  convert result' using 1 <;> ring

theorem northwest_diagonal (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside (3/2) (5/2) := by
  have h := northwest_diagonal_interval p hf hb (1/2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem northwest_long_diagonal (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside (139/100) (261/100) := by
  have h := northwest_diagonal_interval p hf hb (61/100) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem northwest_north (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside 2 (5/2) := by
  let C := (pullX (owners p 7)).translated 2 2
  let W := (pullX (owners p 8)).translated 2 2
  have nw := northwest_pair p hf hb
  have markC : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markW : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have markN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markS : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have tipW : (owners p 8).Inside 1 (239/100) := by
    have h := local_wall_segment p mmmp hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have segment : ∀ y : ℝ, 0≤y → y≤39/100 → W.Inside 1 y := by
    intro y yn yu
    have h := inside_segment (owners p 8) 1 2 1 (239/100) ((100/39)*y)
      (left_origin p hf hb) tipW (by nlinarith only [yn]) (by nlinarith only [yu])
    norm_num [W,inside_translated_iff,inside_pullX]
    convert h using 1 <;> ring
  have cut : 2≤centerY (owners p 8) := by
    have h := (hb 0).1
    simpa [mmmp,wallFrame,localFrame,wallOwner] using h
  have centerW : centerY W=centerY (owners p 8)-2 := by
    dsimp [W,OpenSquare.translated,pullX,centerY]
    linear_combination -2*(owners p 8).unit_normal
  have answer := C1092MMMPCenterCrosspoint.point C W (side_gt p 7) (side_same p 7 8)
    (by norm_num [C,inside_translated_iff,inside_pullX]; exact northwest_center p hf hb)
    (by norm_num [C,inside_translated_iff,inside_pullX]; exact markC)
    (by norm_num [C,inside_translated_iff,inside_pullX]; exact nw.1)
    (by norm_num [C,inside_translated_iff,inside_pullX]; exact nw.2)
    (by
      norm_num [C,inside_translated_iff,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,markN⟩)
    (by
      norm_num [C,inside_translated_iff,inside_pullX]
      intro own
      exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,markS⟩)
    (by norm_num [W,inside_translated_iff,inside_pullX]; exact markW)
    (by norm_num [W,inside_translated_iff,inside_pullX]; exact (wall_auxiliaries p hb).1)
    segment
    (by
      intro x y own
      have h := (inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own)
      have box := p.contained _ _ _ h
      linarith only [box.1])
    (by rw [centerW]; linarith only [cut])
    (by
      intro x y own
      have first := (inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own.1)
      have last := (inside_pullX _ _ _).mp ((inside_translated_iff _ _ _ _ _).mp own.2)
      exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨first,last⟩)
  norm_num [C,inside_translated_iff,inside_pullX] at answer
  exact answer

#print axioms northwest_diagonal_interval
#print axioms northwest_north
end N12Compact.C1092MMMPPointCore
