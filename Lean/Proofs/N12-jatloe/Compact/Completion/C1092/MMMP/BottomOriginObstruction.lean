import Compact.Completion.C1092.MMMP.BottomOwnMargin

/-! Completed local Theorem 1 of DOUBLE-RIGHT-BOTTOM-ORIGIN. The two
surviving face axes are derived from strict anchors of the same squares,
then excluded by their whole-square supports. No angular case is omitted. -/
namespace N12Compact.C1092MMMPBottomOriginObstruction
open C977ChainBridge ThreeSquare S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

private theorem alternatives (C R : OpenSquare) (same : C.side=R.side)
    (cp : 0<C.c) (sp : 0<C.s) (bp : 0<R.c) (tp : 0<R.s)
    (z : ℝ) (small : z<2/5)
    (J : C.Inside (13/50) 0) (Z : C.Inside 1 z)
    (S : R.Inside (543/500) 0) (B : R.Inside 1 (2/5))
    (apart : ∀ x y, ¬(C.Inside x y ∧ R.Inside x y)) :
    C.loU+C.side≤lower R C.c C.s ∨ upper C R.c R.s≤R.loU := by
  have axes := CongruentSAT.faceSeparation_of_disjoint C R same apart
  change pairRadius C R≤|C.c*(centerX R-centerX C)+C.s*(centerY R-centerY C)| ∨
    pairRadius C R≤|-C.s*(centerX R-centerX C)+C.c*(centerY R-centerY C)| ∨
    pairRadius R C≤|R.c*(centerX R-centerX C)+R.s*(centerY R-centerY C)| ∨
    pairRadius R C≤|-R.s*(centerX R-centerX C)+R.c*(centerY R-centerY C)| at axes
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius R nx ny=radius)
      (sep : radius≤|nx*(centerX R-centerX C)+ny*(centerY R-centerY C)|) :=
    separated C R nx ny (by rwa [identity])
  have horizontal (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (positive : 0<nx) (sep : upper R nx ny≤lower C nx ny) : False := by
    have first := (strict_bounds C _ _ nx ny unit J).1
    have last := (strict_bounds R _ _ nx ny unit S).2
    linarith only [first,last,positive,sep]
  have negativeX (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (negative : nx<0) (sep : upper C nx ny≤lower R nx ny) : False := by
    have first := (strict_bounds C _ _ nx ny unit J).2
    have last := (strict_bounds R _ _ nx ny unit S).1
    linarith only [first,last,negative,sep]
  have vertical (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (positive : 0<ny) (sep : upper R nx ny≤lower C nx ny) : False := by
    have first := (strict_bounds C _ _ nx ny unit Z).1
    have last := (strict_bounds R _ _ nx ny unit B).2
    have gap := mul_pos positive (sub_pos.mpr small)
    nlinarith only [first,last,sep,gap]
  rcases axes with cu|cv|ru|rv
  · rcases split _ _ _ (parallel_radius C R) cu with forward|reverse
    · exact Or.inl (by simpa only [(ownU C).2] using forward)
    · exact (horizontal _ _ C.unit_normal cp reverse).elim
  · rcases split _ _ _ (transverse_radius C R) cv with forward|reverse
    · exact (negativeX _ _ (by nlinarith only [C.unit_normal])
        (by linarith only [sp]) forward).elim
    · exact (vertical _ _ (by nlinarith only [C.unit_normal]) cp reverse).elim
  · have identity : supportRadius C R.c R.s+supportRadius R R.c R.s=pairRadius R C := by
      rw [add_comm]
      exact parallel_radius R C
    rcases split _ _ _ identity ru with forward|reverse
    · exact Or.inr (by simpa only [(ownU R).1] using forward)
    · exact (horizontal _ _ R.unit_normal bp reverse).elim
  · have identity : supportRadius C (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R C := by
      rw [add_comm]
      exact transverse_radius R C
    rcases split _ _ _ identity rv with forward|reverse
    · exact (negativeX _ _ (by nlinarith only [R.unit_normal])
        (by linarith only [tp]) forward).elim
    · exact (vertical _ _ (by nlinarith only [R.unit_normal]) bp reverse).elim

/-- The paper's complete local obstruction, including the genuine wall
and all strict or missing anchors of the two actual squares. -/
theorem impossible (C W : OpenSquare) (side : 1<C.side)
    (same : C.side=W.side) (cn : Normal C.c C.s)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (A : ¬C.Inside (2/5) 1) (H : ¬C.Inside (1/2) 1)
    (S : W.Inside (543/500) 0) (G : W.Inside 1 (13/50))
    (B : W.Inside 1 (2/5)) (P : ¬W.Inside 1 0)
    (wall : ∀ x y, W.Inside x y → x≤2)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have missingG : ¬C.Inside 1 (13/50) := fun own => apart _ _ ⟨own,G⟩
  have entrance := C1092MMMPPositiveInwardHalfangle.entrance C side cn M I J O A missingG
  have point := C1092MMMPPositiveInwardHalfangle.point C side cn M I J O A H missingG
  obtain ⟨R,shape,inside,data⟩ := C1092MMMPBottomBoundaryOrder.exists_frame
    C W side same cn M I J O A H S G B P wall apart
  have sameR : C.side=R.side := same.trans shape.symm
  have s := (inside _ _).mpr S
  have b := (inside _ _).mpr B
  have axes := alternatives C R sameR
    (by linarith only [(normal_bounds cn).1]) entrance.2.1 data.cosine data.sine
    (C1092WallProfileScalars.half C.c C.s)
    (by linarith only [entrance.2.2.2.2.1]) J point s b
    (fun x y own => apart x y ⟨own.1,(inside x y).mp own.2⟩)
  rcases axes with own|boundary
  · exact C1092MMMPBottomOwnMargin.own_normal_impossible C R side sameR cn
      entrance.2.1 entrance.1 s data own
  · exact C1092MMMPBottomBoundaryMargin.boundary_normal_impossible C R side sameR cn
      entrance.2.2.2.2.2.1 entrance.2.2.2.2.2.2 entrance.2.1 entrance.2.2.2.2.1
      entrance.1 M data boundary

#print axioms impossible
end N12Compact.C1092MMMPBottomOriginObstruction
