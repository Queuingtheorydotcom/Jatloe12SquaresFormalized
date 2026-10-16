import Compact.Completion.C1092.MMMP.PointCore
import Compact.Completion.C1092.MMMP.NortheastSign
import Compact.Completion.C1092.MMMP.EndingAxes

/-! The local northeast sign theorem applied to the original MMMP owners.
Every omitted point below has one named genuine foreign owner. -/
namespace N12Compact.C1092MMMPNortheastActualSign
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore C1092MMMPEndingAxes C977CornerCubic
set_option Elab.async false

structure PositiveActual (p : NormalizedPacking) (N : OpenSquare) : Prop where
  side : N.side=(owners p 6).side
  actual : ∀ x y, N.Inside x y↔(owners p 6).Inside (2+x) (2+y)
  normal : Normal N.c N.s
  positive : 0<N.s

theorem exists_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : ∃ N : OpenSquare, PositiveActual p N := by
  classical
  let q := (owners p 6).translated 2 2
  obtain ⟨N,nc,ns,nside,ninside,_⟩ := ClosedFrames.canonical_frame q
  let C := clockwise ((owners p 7).translated 2 2)
  let B := clockwise N
  have Cin (x y : ℝ) : C.Inside x y↔(owners p 7).Inside (2+y) (2-x) := by
    simpa only [C,inside_clockwise,inside_translated_iff,sub_eq_add_neg]
  have Bin (x y : ℝ) : B.Inside x y↔(owners p 6).Inside (2+y) (2-x) := by
    dsimp only [B]
    rw [inside_clockwise,ninside]
    simpa only [q,sub_eq_add_neg] using inside_translated_iff (owners p 6) 2 2 y (-x)
  have nwMark : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have neMark : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have swMark : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have topMark : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have leftTip : (owners p 8).Inside 1 (239/100) := by
    have h := local_wall_segment p mmmp hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have rightTip : (owners p 10).Inside 3 (239/100) := by
    have h := local_wall_segment p mmmp hb 2 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have middle : (owners p 7).Inside 2 (239/100) := by
    have h := inside_segment (owners p 7) 2 2 2 (5/2) (39/50)
      (northwest_center p hf hb) (northwest_north p hf hb) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have same : C.side=B.side := by
    change (owners p 7).side=N.side
    exact (side_same p 7 6).trans nside.symm
  have positive := C1092MMMPNortheastSign.positive C B (side_gt p 7) same nc ns
    (by apply (Cin _ _).mpr; norm_num; exact northwest_center p hf hb)
    (by apply (Cin _ _).mpr; norm_num; exact northwest_north p hf hb)
    (by apply (Cin _ _).mpr; norm_num; exact northwest_left p hf hb)
    (by apply (Cin _ _).mpr; norm_num; exact nwMark)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨own',swMark⟩)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨own',neMark⟩)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨own',leftTip⟩)
    (by apply (Bin _ _).mpr; norm_num; exact neMark)
    (by apply (Bin _ _).mpr; norm_num; exact (northeast_pair p hf hb).2)
    (by apply (Bin _ _).mpr; norm_num; exact (northeast_pair p hf hb).1)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨own',middle⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨own',rightTip⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨own',topMark⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨own',corner⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 7 (by decide) _ _ ⟨own',northwest_north p hf hb⟩)
    (by
      intro x y own
      exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨(Cin _ _).mp own.1,(Bin _ _).mp own.2⟩)
  have pos : 0<N.s := positive
  refine ⟨N,nside,?_,⟨pos.le,?_,N.unit_normal⟩,pos⟩
  · intro x y
    rw [ninside]
    exact inside_translated_iff _ _ _ _ _
  · simpa only [abs_of_pos pos] using ns

#print axioms exists_positive
end N12Compact.C1092MMMPNortheastActualSign
