import Compact.Completion.C1092.MMMP.BottomPair
import Compact.Completion.C1092.MMMP.ShortBarNegative

/-! A genuine right F8 forces the southeast inward pair and its strictly
positive canonical sign. The negative sign is excluded by the same actual
bottom wall and the whole strict right segment; no G8 owner is assumed. -/
namespace N12Compact.C1092MMMPSoutheastSign
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092AuxiliaryCover
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore C977CornerCubic
set_option Elab.async false

theorem inward_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (near : (owners p 10).Inside 3 (87/50)) :
    (owners p 5).Inside 2 (87/50) ∧ (owners p 5).Inside (113/50) 2 := by
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have f : (owners p 5).Inside 2 (87/50) := by
    rcases C1092MMMMEntrance.southeast_f_cover p hf with h|h|h
    · exact h
    · exact False.elim (owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom.1⟩)
    · exact False.elim (owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,near⟩)
  have g : (owners p 5).Inside (113/50) 2 := by
    by_contra missing
    rcases southeast_g_cover p hf with h|h|h
    · exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom.2⟩
    · exact missing h
    · exact C1092MixedSpan.impossible (owners p 5) (side_gt p 5) f h missing
        (fun own => owners_disjoint p hf 5 10 (by decide) _ _ ⟨own,near⟩)
        (fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bottom.2⟩)
        (fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bottom.1⟩)
  exact ⟨f,g⟩

private noncomputable def chart (q : OpenSquare) : OpenSquare :=
  (pullSwap (pullY q)).translated 2 2

private theorem inside_chart (q : OpenSquare) (x y : ℝ) :
    (chart q).Inside x y ↔ q.Inside (2+y) (2-x) := by
  simp only [chart,inside_translated_iff,inside_pullSwap,inside_pullY]
  rw [show 4-(2+x)=2-x by ring]

private theorem center_chart (q : OpenSquare) : centerY (chart q)=centerX q-2 := by
  dsimp [chart,OpenSquare.translated,pullSwap,pullY,centerY,centerX]
  linear_combination -2*q.unit_normal

structure PositiveActual (p : NormalizedPacking) (C : OpenSquare) : Prop where
  side : C.side=(owners p 5).side
  actual : ∀ x y, C.Inside x y ↔ (owners p 5).Inside (2+y) (2-x)
  normal : Normal C.c C.s
  positive : 0<C.s

theorem exists_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (near : (owners p 10).Inside 3 (87/50)) :
    ∃ C : OpenSquare, PositiveActual p C := by
  classical
  have inward := inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have markC : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have markW : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have tipW : (owners p 9).Inside (239/100) 1 := by
    have h := local_wall_segment p mmmp hb 1 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have rightBar : ∀ x : ℝ, 0≤x → x≤13/50 → (owners p 10).Inside 3 (2-x) := by
    intro x xn xu
    have h := inside_segment (owners p 10) 3 2 3 (87/50) ((50/13)*x)
      (right_origin p hf hb) near (by nlinarith only [xn]) (by nlinarith only [xu])
    convert h using 1 <;> ring
  obtain ⟨C,cp,canon,shape,inside,_⟩ := ClosedFrames.canonical_frame (chart (owners p 5))
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2+y) (2-x) :=
    (inside x y).trans (inside_chart _ x y)
  have positive : 0<C.s := by
    apply lt_of_not_ge
    intro nonpositive
    have cn : Normal C.c (-C.s) := ⟨by linarith only [nonpositive],
      by simpa only [abs_of_nonpos nonpositive] using canon,
      by nlinarith only [C.unit_normal]⟩
    let W := chart (owners p 9)
    have cut : 2≤centerX (owners p 9) := by
      have h : 2≤centerY (pullSwap (owners p 9)) := by
        simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 1).1
      have center : centerY (pullSwap (owners p 9))=centerX (owners p 9) := by
        dsimp [centerY,centerX,pullSwap]
        ring
      rwa [center] at h
    apply C1092MMMPShortBarNegative.impossible C W cn
      (by rw [shape]; exact side_gt p 5) (shape.trans (side_same p 5 9))
    · apply (actual _ _).mpr
      norm_num
      exact markC
    · apply (actual _ _).mpr
      norm_num
      exact inward.2
    · apply (actual _ _).mpr
      norm_num
      exact inward.1
    · intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 7 (by decide) _ _ ⟨h,northwest_center p hf hb⟩
    · intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨h,bottom.1⟩
    · intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,near⟩
    · intro x xn xu own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,rightBar x xn xu⟩
    · apply (inside_chart _ _ _).mpr
      norm_num
      exact markW
    · apply (inside_chart _ _ _).mpr
      norm_num
      exact bottom.2
    · apply (inside_chart _ _ _).mpr
      norm_num
      exact tipW
    · intro x y own
      have h := (inside_chart _ _ _).mp own
      have box := p.contained _ _ _ h
      linarith only [box.2.2.1]
    · dsimp [W]
      rw [center_chart]
      linarith only [cut]
    · intro x y own
      exact owners_disjoint p hf 5 9 (by decide) _ _
        ⟨(actual _ _).mp own.1,(inside_chart _ _ _).mp own.2⟩
  refine ⟨C,shape,actual,?_,positive⟩
  exact ⟨positive.le,by simpa only [abs_of_pos positive] using canon,C.unit_normal⟩

#print axioms inward_pair
#print axioms exists_positive
end N12Compact.C1092MMMPSoutheastSign
