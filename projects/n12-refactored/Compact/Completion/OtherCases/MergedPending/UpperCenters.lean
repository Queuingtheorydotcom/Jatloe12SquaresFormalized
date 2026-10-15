import Compact.Completion.OtherCases.MergedPending.UpperSectors
import Compact.Completion.OtherCases.MergedPending.UpperCenterCore

/-! Actual center and southwest-face cuts for all three pending merged
families. The C700 statement uses the same complete transposed chart as
its UpperResidue. The negative merged-frame branch remains explicit in
UpperSectors; no whole-family impossibility is asserted here. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem upper_nonnegative_center (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (hc : 0<H.c) (hs : 0≤H.s) (canonical : H.s≤H.c)
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) : H.Inside 2 2 := by
  have sides (m : Nat) : (owner p m).side=p.commonSide := p.congruent _
  have size : 1<H.side := by simpa only [shape] using side p 3072
  have same : H.side=(owner p 32768).side :=
    shape.trans ((sides 3072).trans (sides 32768).symm)
  have marks := upper_merged_markers k p hf member
  have labels := common_labels k p hf
  have left := (auxiliary_exact p 4096 11 (by norm_num)).mpr labels.left.2
  have far := (auxiliary_exact p 32768 3 (by norm_num)).mpr labels.top.1
  have near := (auxiliary_exact p 32768 14 (by norm_num)).mpr labels.top.2
  have mark := seed _ p hf 32768 (common_member k 32768 (by decide))
    (2,1543/500) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints] at left far near mark
  have foreign (m : Nat) (hm : m∈family k) (different : 3072≠m)
      (x y : ℝ) (point : (owner p m).Inside x y) : ¬H.Inside x y := fun own =>
    apart _ p hf 3072 m member hm different _ _ ⟨(inside _ _).mp own,point⟩
  exact upper_center H (owner p 32768) size same (box p 32768) hc hs canonical
    ((inside _ _).mpr marks.1) ((inside _ _).mpr marks.2)
    (foreign 16 (common_member k 16 (by decide)) (by decide) _ _
      ((walls k p hf).topSingleton _ le_rfl (by norm_num)))
    (foreign 32768 (common_member k 32768 (by decide)) (by decide) _ _ near)
    (foreign 4096 (common_member k 4096 (by decide)) (by decide) _ _ left) mark far
    (fun x y points => apart _ p hf 3072 32768 member
      (common_member k 32768 (by decide)) (by decide) _ _
        ⟨(inside _ _).mp points.1,points.2⟩)

theorem upper_nonnegative_residue (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (A H : OpenSquare) (ac : 0<A.c) (canonicalA : |A.s|≤A.c)
    (hc : 0<H.c) (hs : 0≤H.s) (canonicalH : H.s≤H.c)
    (sa : A.side=(owner p 256).side) (sh : H.side=(owner p 3072).side)
    (ia : ∀ x y,A.Inside x y↔(owner p 256).Inside x y)
    (ih : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    A.s<0 ∧ (owner p 1).Inside 1 1 ∧ H.Inside 2 2 ∧
      A.loV+A.side≤2*(A.c-A.s) := by
  have center := upper_nonnegative_center k p hf member H hc hs canonicalH sh ih
  have result := ((upper_data k p hf member).reframe A H sa sh ia ih).nonnegative_residue
    ac canonicalA ⟨hs,canonicalH,H.unit_normal⟩ center
    ((ia _ _).mpr (southwest_crosspoints k p hf).1)
  exact ⟨result.1,result.2.1,center,result.2.2⟩

theorem c700_transposed_nonnegative_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) (H : OpenSquare)
    (hc : 0<H.c) (hs : 0≤H.s) (canonical : H.s≤H.c)
    (shape : H.side=(owner p 1536).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 1536).Inside y x) : H.Inside 2 2 := by
  have sides (m : Nat) : (owner p m).side=p.commonSide := p.congruent _
  have size : 1<H.side := by simpa only [shape] using side p 1536
  have same : H.side=(pullSwap (owner p 16384)).side :=
    shape.trans ((sides 1536).trans (sides 16384).symm)
  have marks := c700_merged_markers p hf
  have labels := common_labels .c700 p hf
  have bottom := (auxiliary_exact p 8192 6 (by norm_num)).mpr labels.bottom.1
  have far := (auxiliary_exact p 16384 18 (by norm_num)).mpr (c700_right_labels p hf).2
  have near := (auxiliary_exact p 16384 8 (by norm_num)).mpr (c700_right_labels p hf).1
  have mark := seed _ p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints] at bottom far near mark
  have foreign (m : Nat) (hm : m∈family .c700) (different : 1536≠m)
      (x y : ℝ) (point : (owner p m).Inside y x) : ¬H.Inside x y := fun own =>
    apart _ p hf 1536 m (by decide +kernel) hm different _ _ ⟨(inside _ _).mp own,point⟩
  exact upper_center H (pullSwap (owner p 16384)) size same
    (container_pullSwap _ (box p 16384)) hc hs canonical
    ((inside _ _).mpr marks.1) ((inside _ _).mpr marks.2)
    (foreign 32 (by decide +kernel) (by decide) _ _
      (c700_right_singleton p hf _ le_rfl (by norm_num)))
    (foreign 16384 (by decide +kernel) (by decide) _ _ near)
    (foreign 8192 (by decide +kernel) (by decide) _ _ bottom)
    ((inside_pullSwap _ _ _).mpr mark) ((inside_pullSwap _ _ _).mpr far)
    (fun x y points => apart _ p hf 1536 16384
      (by decide +kernel) (by decide +kernel) (by decide) _ _
      ⟨(inside _ _).mp points.1,(inside_pullSwap _ _ _).mp points.2⟩)

theorem c700_transposed_nonnegative_residue (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700)
    (A H : OpenSquare) (ac : 0<A.c) (canonicalA : |A.s|≤A.c)
    (hc : 0<H.c) (hs : 0≤H.s) (canonicalH : H.s≤H.c)
    (sa : A.side=(owner p 256).side) (sh : H.side=(owner p 1536).side)
    (ia : ∀ x y,A.Inside x y↔(owner p 256).Inside y x)
    (ih : ∀ x y,H.Inside x y↔(owner p 1536).Inside y x) :
    A.s<0 ∧ (owner p 2).Inside 1 1 ∧ H.Inside 2 2 ∧
      A.loV+A.side≤2*(A.c-A.s) := by
  have center := c700_transposed_nonnegative_center p hf H hc hs canonicalH sh ih
  have ai (x y : ℝ) : A.Inside x y↔(pullSwap (owner p 256)).Inside x y :=
    (ia x y).trans (inside_pullSwap _ _ _).symm
  have hi (x y : ℝ) : H.Inside x y↔(pullSwap (owner p 1536)).Inside x y :=
    (ih x y).trans (inside_pullSwap _ _ _).symm
  have result := ((c700_transposed_data p hf).reframe A H sa sh ai hi).nonnegative_residue
    ac canonicalA ⟨hs,canonicalH,H.unit_normal⟩ center
    ((ia _ _).mpr (southwest_crosspoints .c700 p hf).2)
  exact ⟨result.1,(inside_pullSwap _ _ _).mp result.2.1,center,result.2.2⟩

end
#print axioms upper_nonnegative_residue
#print axioms c700_transposed_nonnegative_residue
end N12Compact.MergedPending
