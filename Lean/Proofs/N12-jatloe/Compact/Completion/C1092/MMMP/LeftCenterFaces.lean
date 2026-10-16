import Compact.Completion.C1092.WholeSupports
import Compact.Geometry.C977CornerCubic

/-! The actual left square's upper face and center abscissa, forced by
its strict origin/near point, two true omissions and nonnegative center
ordinate. Both canonical signs include their axial endpoints. -/
namespace N12Compact.C1092MMMPLeftCenterFaces
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

private theorem origin_faces (L : OpenSquare) (O : L.Inside 0 0) :
    L.loU<0 ∧ 0<L.loU+L.side ∧ L.loV<0 ∧ 0<L.loV+L.side := by
  simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using O

theorem positive (L : OpenSquare) (cn : Normal L.c L.s) (side : 1<L.side)
    (O : L.Inside 0 0) (T : L.Inside 0 (39/100))
    (H : ¬L.Inside 0 (1/2)) (X : ¬L.Inside (1/2) 0)
    (cut : 0≤centerY L) :
    0<L.s ∧ L.loU+L.side≤L.s/2 ∧ centerX L<0 := by
  classical
  have cb := normal_bounds cn
  have cp : 0<L.c := by linarith only [cb.1]
  have o := origin_faces L O
  have hExit : L.loU+L.side≤L.s/2 ∨ L.loV+L.side≤L.c/2 := by
    by_cases u : L.loU+L.side≤L.s/2
    · exact Or.inl u
    · apply Or.inr
      apply le_of_not_gt
      intro v
      apply H
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [T.1,T.2.2.1,u,v,cp,cn.1]
  have xExit : L.loU+L.side≤L.c/2 ∨ -L.s/2≤L.loV := by
    by_cases u : L.loU+L.side≤L.c/2
    · exact Or.inl u
    · apply Or.inr
      apply le_of_not_gt
      intro v
      apply X
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [o.1,o.2.2.2,u,v,cp,cn.1]
  have upperU : L.loU+L.side≤L.s/2 := by
    rcases hExit with u|v
    · exact u
    · rcases xExit with u|lo
      · have first := mul_nonneg cn.1 (sub_nonneg.mpr u)
        have last := mul_nonneg cp.le (sub_nonneg.mpr v)
        have strict := mul_pos
          (show 0<L.side-L.c by linarith only [side,cb.2.1])
          (show 0<L.c+L.s by linarith only [cp,cn.1])
        dsimp [centerY] at cut
        nlinarith only [first,last,strict,cut]
      · linarith only [v,lo,side,cb.2.2.2.2.2]
  have projection : L.c*centerX L+L.s*centerY L=L.loU+L.side/2 := by
    dsimp [centerX,centerY]
    linear_combination (L.loU+L.side/2)*L.unit_normal
  have yProduct := mul_nonneg cn.1 cut
  have cx : L.c*centerX L<0 := by
    nlinarith only [projection,upperU,side,cb.2.2.2.1,yProduct]
  have center : centerX L<0 := by
    apply lt_of_not_ge
    intro failure
    have bad := mul_nonneg cp.le failure
    linarith only [cx,bad]
  have sine : 0<L.s := by
    apply lt_of_not_ge
    intro failure
    have zero : L.s=0 := le_antisymm failure cn.1
    have upper : L.loU+L.side≤0 := by simpa only [zero,zero_div] using upperU
    linarith only [upper,o.2.1]
  exact ⟨sine,upperU,center⟩

theorem negative (L : OpenSquare) (cn : Normal L.c (-L.s)) (side : 1<L.side)
    (O : L.Inside 0 0) (T : L.Inside 0 (39/100))
    (H : ¬L.Inside 0 (1/2)) (X : ¬L.Inside (1/2) 0)
    (cut : 0≤centerY L) :
    0< -L.s ∧ L.loV+L.side≤L.c/2 ∧ centerX L<0 := by
  classical
  have cb := normal_bounds cn
  have cp : 0<L.c := by linarith only [cb.1]
  have sn : L.s≤0 := by linarith only [cn.1]
  have o := origin_faces L O
  have hExit : L.s/2≤L.loU ∨ L.loV+L.side≤L.c/2 := by
    by_cases u : L.s/2≤L.loU
    · exact Or.inl u
    · apply Or.inr
      apply le_of_not_gt
      intro v
      apply H
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [o.2.1,T.2.2.1,u,v,cp,sn]
  have xExit : L.loU+L.side≤L.c/2 ∨ L.loV+L.side≤-L.s/2 := by
    by_cases u : L.loU+L.side≤L.c/2
    · exact Or.inl u
    · apply Or.inr
      apply le_of_not_gt
      intro v
      apply X
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [o.1,o.2.2.1,u,v,cp,sn]
  have upperV : L.loV+L.side≤L.c/2 := by
    rcases hExit with u|v
    · rcases xExit with hi|hi
      · linarith only [u,hi,side,cb.2.2.2.2.2]
      · have first := mul_nonpos_of_nonpos_of_nonneg sn (sub_nonneg.mpr u)
        have last := mul_nonneg cp.le (sub_nonneg.mpr hi)
        have strict := mul_pos
          (show 0<L.side+L.s by linarith only [side,cb.2.2.2.1])
          (show 0<L.c-L.s by linarith only [cp,sn])
        dsimp [centerY] at cut
        nlinarith only [first,last,strict,cut]
    · exact v
  have projection : -L.s*centerX L+L.c*centerY L=L.loV+L.side/2 := by
    dsimp [centerX,centerY]
    linear_combination (L.loV+L.side/2)*L.unit_normal
  have yProduct := mul_nonneg cp.le cut
  have cx : (-L.s)*centerX L<0 := by
    nlinarith only [projection,upperV,side,cb.2.1,yProduct]
  have center : centerX L<0 := by
    apply lt_of_not_ge
    intro failure
    have bad := mul_nonneg cn.1 failure
    linarith only [cx,bad]
  have nonzero : -L.s≠0 := by
    intro zero
    rw [zero,zero_mul] at cx
    linarith only [cx]
  exact ⟨lt_of_le_of_ne cn.1 (Ne.symm nonzero),upperV,center⟩

#print axioms positive
#print axioms negative
end N12Compact.C1092MMMPLeftCenterFaces
