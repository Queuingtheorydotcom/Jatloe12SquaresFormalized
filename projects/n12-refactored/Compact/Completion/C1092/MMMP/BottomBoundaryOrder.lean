import Compact.Completion.C1092.MMMP.PositiveInwardHalfangle
import Compact.Completion.OtherCases.WallProfile.SupportGeometry

/-! Transcription of DOUBLE-RIGHT-BOTTOM-ORIGIN section 1.2. The actual
boundary square is retained by face reindexing; its angle is not restricted
to a canonical octant. The two remaining support sources of sections 2--3
are not ruled out by this module. -/
namespace N12Compact.C1092MMMPBottomBoundaryOrder
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
set_option Elab.async false

structure Data (C R : OpenSquare) : Prop where
  cosine : 0<R.c
  sine : 0<R.s
  lowerU : R.c+R.s*C1092WallProfileScalars.half C.c C.s≤R.loU
  markerU : R.loU<(543/500)*R.c
  markerV : R.loV< -(543/500)*R.s
  wall : R.c*(R.loU+R.side)-R.s*R.loV≤2
  angle : 0<R.s*C.c-R.c*C.s

private theorem angle_order (C R : OpenSquare) (cn : Normal C.c C.s)
    (cosine : 2331/2669<C.c) (sp : 0<C.s)
    (rp : 0<R.c) (tp : 0<R.s) (side : 1<R.side)
    (lower : R.c+R.s*C1092WallProfileScalars.half C.c C.s≤R.loU)
    (marker : R.loV< -(543/500)*R.s)
    (wall : R.c*(R.loU+R.side)-R.s*R.loV≤2) :
    0<R.s*C.c-R.c*C.s := by
  let c := C.c
  let s := C.s
  let b := R.c
  let t := R.s
  let z := C1092WallProfileScalars.half c s
  have cp : 0<c := by dsimp [c]; linarith only [cosine]
  have zp : 0<z := by
    dsimp [z,C1092WallProfileScalars.half]
    exact div_pos sp (by linarith only [cp])
  have angle : z*(1+c)=s := by
    dsimp [z,C1092WallProfileScalars.half]
    field_simp [show 1+c≠0 by linarith only [cp]]
  have lowerScaled := mul_le_mul_of_nonneg_left lower rp.le
  have markerScaled := mul_lt_mul_of_pos_left marker tp
  have excess := mul_pos rp (sub_pos.mpr side)
  have wallGap : b*t*z<1-b-(43/500)*t^2 := by
    dsimp [b,t,c,s,z]
    nlinarith only [lowerScaled,markerScaled,excess,wall,R.unit_normal]
  apply lt_of_not_ge
  intro reversed
  have weak : t*c≤b*s := by dsimp [b,t,c,s]; linarith only [reversed]
  have comparison := mul_nonneg (sub_nonneg.mpr weak)
    (show 0≤b*s+t*c by positivity)
  have cosineOrder : c≤b := by
    apply le_of_not_gt
    intro wrong
    have product := mul_pos (sub_pos.mpr wrong)
      (show 0<c+b by linarith only [cp,rp])
    have identity : (b*s-t*c)*(b*s+t*c)=b^2-c^2 := by
      dsimp [b,t,c,s]
      linear_combination R.c^2*C.unit_normal-C.c^2*R.unit_normal
    rw [identity] at comparison
    nlinarith only [comparison,product]
  have sineOrder : t≤s := by
    have comparison := mul_nonneg (sub_nonneg.mpr cosineOrder)
      (show 0≤b+c by linarith only [rp,cp])
    apply le_of_not_gt
    intro wrong
    have product := mul_pos (sub_pos.mpr wrong)
      (show 0<t+s by linarith only [tp,sp])
    dsimp [b,t,c,s] at comparison product
    nlinarith only [comparison,product,R.unit_normal,C.unit_normal]
  have halfOrder : t≤z*(1+b) := by
    have extra := mul_nonneg zp.le (sub_nonneg.mpr cosineOrder)
    nlinarith only [angle,extra,sineOrder]
  have halfScaled := mul_le_mul_of_nonneg_left halfOrder (mul_nonneg rp.le tp.le)
  have wallScaled := mul_lt_mul_of_pos_right wallGap
    (show 0<1+b by linarith only [rp])
  have coefficient : (457/500)-(543/500)*b≤0 := by
    dsimp [c] at cosineOrder
    linarith only [cosineOrder,cosine]
  have impossible := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) coefficient
  have identity : (1-b-(43/500)*t^2)*(1+b)-b*t^2=
      t^2*((457/500)-(543/500)*b) := by
    dsimp [b,t]
    linear_combination -R.unit_normal
  nlinarith only [halfScaled,wallScaled,impossible,identity]

/-- The positive boundary frame and its strict angle order are forced
by the same two actual squares and the genuine physical wall. -/
theorem exists_frame (C W : OpenSquare) (side : 1<C.side)
    (same : C.side=W.side) (cn : Normal C.c C.s)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (A : ¬C.Inside (2/5) 1) (H : ¬C.Inside (1/2) 1)
    (S : W.Inside (543/500) 0) (G : W.Inside 1 (13/50))
    (B : W.Inside 1 (2/5)) (P : ¬W.Inside 1 0)
    (wall : ∀ x y, W.Inside x y → x≤2)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) :
    ∃ R : OpenSquare, R.side=W.side ∧
      (∀ x y, R.Inside x y ↔ W.Inside x y) ∧ Data C R := by
  have missingG : ¬C.Inside 1 (13/50) := fun own => apart _ _ ⟨own,G⟩
  have entrance := C1092MMMPPositiveInwardHalfangle.entrance C side cn M I J O A missingG
  have point := C1092MMMPPositiveInwardHalfangle.point C side cn M I J O A H missingG
  let z := C1092WallProfileScalars.half C.c C.s
  have zp : 0<z := entrance.2.2.2.1
  have small : z<13/50 := entrance.2.2.2.2.1
  obtain ⟨R,rp,tn,shape,inside,_⟩ := Completion.OtherCases.WallProfile.positive_frame W
  have s := (inside _ _).mpr S
  have g := (inside _ _).mpr G
  have b := (inside _ _).mpr B
  have missing : ¬R.Inside 1 0 := fun own => P ((inside _ _).mp own)
  have tp : 0<R.s := by
    rcases tn.eq_or_lt with zero | positive
    · have axis : R.s=0 := zero.symm
      apply False.elim
      apply missing
      simp only [OpenSquare.Inside,InBands,axis,mul_zero,zero_mul,neg_zero,
        zero_add,add_zero,mul_one] at s g ⊢
      exact ⟨g.1,g.2.1,s.2.2.1,s.2.2.2⟩
    · exact positive
  have absent : ¬R.Inside 1 z :=
    fun own => apart _ _ ⟨point,(inside _ _).mp own⟩
  have lower : R.c+R.s*z≤R.loU := by
    apply le_of_not_gt
    intro low
    apply absent
    have u := mul_pos tp (show 0<2/5-z by linarith only [small])
    have vl := mul_pos rp zp
    have vh := mul_pos rp (show 0<13/50-z by linarith only [small])
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [low,s.2.2.1,b.2.1,g.2.2.2,u,vl,vh,tp]
  have markerU : R.loU<(543/500)*R.c := by linarith only [s.1]
  have markerV : R.loV< -(543/500)*R.s := by linarith only [s.2.2.1]
  have box := square_support_bound R 1 0 2
    (by intro x y own; simpa using wall x y ((inside _ _).mp own))
  norm_num [squareRadius,abs_of_pos rp,abs_of_pos tp] at box
  have wallFace : R.c*(R.loU+R.side)-R.s*R.loV≤2 := by
    dsimp [centerX] at box
    nlinarith only [box]
  have order := angle_order C R cn entrance.2.2.2.2.2.1 entrance.2.1 rp tp
    (by rw [shape,←same]; exact side) lower markerV wallFace
  exact ⟨R,shape,inside,rp,tp,lower,markerU,markerV,wallFace,order⟩

#print axioms exists_frame
end N12Compact.C1092MMMPBottomBoundaryOrder
