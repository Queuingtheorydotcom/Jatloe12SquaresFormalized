import Compact.Completion.OtherCases.NegativeTripleNorthSeparation

/-! The actual southeast/right separator has positive coordinates. The
genuine bottom-bar alternatives place the southeast upper-right vertex
strictly right of the wall origin and strictly below it. Consequently only
the two positive transverse face normals can separate these two squares.
This is a separator reduction, not the remaining three-square contradiction. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeRightSeparation
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem southeast_vertex_coordinates (E : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t) :
    ClosedInside E (E.c*(E.loU+E.side)+t*(E.loV+E.side))
      (-t*(E.loU+E.side)+E.c*(E.loV+E.side)) ∧
      1<E.c*(E.loU+E.side)+t*(E.loV+E.side) ∧
      -t*(E.loU+E.side)+E.c*(E.loV+E.side)<0 := by
  let U := E.loU+E.side
  let H := E.loV+E.side
  let X := E.c*U+t*H
  let Y := -t*U+E.c*H
  have unit : E.c^2+t^2=1 := by
    simpa only [profile.signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t profile.cosinePositive
    profile.sinePositive.le profile.ordered unit
  have tSquare := mul_pos profile.sinePositive profile.sinePositive
  have cSmall : E.c<1 := by
    nlinarith only [unit,tSquare,profile.cosinePositive]
  have tSmall : t<1 := by linarith only [profile.ordered,cSmall]
  have highU : 1<U := profile.upperU
  have highH : H≤t := profile.upperV
  have firstWeight := mul_pos profile.cosinePositive (sub_pos.mpr highU)
  have sideWeight := mul_pos profile.sinePositive (sub_pos.mpr profile.sideLarge)
  have xLarge : 1<X := by
    rcases profile.bar with lowerFace | lowerVertex
    · have barWeight := mul_nonneg profile.sinePositive.le (sub_nonneg.mpr lowerFace)
      have margin := mul_pos (sub_pos.mpr cSmall)
        (show 0<(4/5)*E.c+t-1/5 by
          linarith only [bounds.1,profile.sinePositive])
      have identity : E.c+t*(1+(4/5)*t-E.c)-1=
          (1-E.c)*((4/5)*E.c+t-1/5) := by
        linear_combination (4/5)*unit
      dsimp only [X,U,H] at firstWeight ⊢
      nlinarith only [firstWeight,sideWeight,barWeight,margin,identity]
    · have barWeight := mul_nonneg profile.sinePositive.le
        (show 0≤1-t*U+E.c*E.loV by
          dsimp only [U]
          linarith only [lowerVertex])
      have sideProduct := mul_pos profile.cosinePositive sideWeight
      have margin := mul_pos (sub_pos.mpr cSmall) (sub_pos.mpr tSmall)
      have identity : E.c*X=U+E.c*t*E.side+t*(E.c*E.loV-t*U) := by
        dsimp only [X,H]
        linear_combination U*unit
      have scaled : E.c*1<E.c*X := by
        nlinarith only [identity,highU,sideProduct,barWeight,margin]
      exact (mul_lt_mul_iff_right₀ profile.cosinePositive).mp scaled
  have ySmall : Y<0 := by
    have first := mul_pos profile.sinePositive (sub_pos.mpr highU)
    have last := mul_nonneg profile.cosinePositive.le (sub_nonneg.mpr highH)
    have margin := mul_pos profile.sinePositive (sub_pos.mpr cSmall)
    dsimp only [Y]
    nlinarith only [first,last,margin]
  have closed := WallProfile.vertex E U H
    (by dsimp only [U]; exact ⟨by linarith only [E.side_pos],le_rfl⟩)
    (by dsimp only [H]; exact ⟨by linarith only [E.side_pos],le_rfl⟩)
  rw [profile.signed] at closed
  refine ⟨?_,xLarge,ySmall⟩
  convert closed using 1 <;> ring

theorem southeast_vertex (E : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t) :
    ∃ x y, ClosedInside E x y ∧ 1<x ∧ y<0 := by
  exact ⟨_,_,southeast_vertex_coordinates E t profile⟩

theorem cone (E R : OpenSquare) (t : ℝ)
    (profile : NegativeTripleFaces.Data E t)
    (elbow : E.Inside (13/50) 0) (origin : R.Inside 1 0)
    (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (sep : upper E nx ny≤lower R nx ny) : 0<nx ∧ 0<ny := by
  have first := (strict_bounds E _ _ nx ny unit elbow).2
  have last := (strict_bounds R _ _ nx ny unit origin).1
  have nxPositive : 0<nx := by linarith only [first,last,sep]
  obtain ⟨x,y,closed,xLarge,ySmall⟩ := southeast_vertex E t profile
  have vertex := (closed_bounds E x y nx ny closed).2
  have nyPositive : 0<ny := by
    apply lt_of_not_ge
    intro nonpositive
    have horizontal := mul_pos nxPositive (sub_pos.mpr xLarge)
    have vertical := mul_nonneg (neg_nonneg.mpr nonpositive)
      (neg_nonneg.mpr ySmall.le)
    nlinarith only [vertex,last,sep,horizontal,vertical]
  exact ⟨nxPositive,nyPositive⟩

theorem separators (E R : OpenSquare) (t : ℝ) (same : E.side=R.side)
    (profile : NegativeTripleFaces.Data E t)
    (right : RightTripleData.RightProfile R)
    (elbow : E.Inside (13/50) 0)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) :
    upper E (-E.s) E.c≤lower R (-E.s) E.c ∨
      upper E (-R.s) R.c≤lower R (-R.s) R.c := by
  have reverse (nx ny : ℝ) (sep : upper R nx ny≤lower E nx ny) :
      upper E (-nx) (-ny)≤lower R (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noU (q : OpenSquare) (cp : 0<q.c) (sn : q.s≤0)
      (sep : upper E q.c q.s≤lower R q.c q.s ∨
        upper R q.c q.s≤lower E q.c q.s) : False := by
    rcases sep with forward | backward
    · have direction := cone E R t profile elbow right.origin q.c q.s q.unit_normal forward
      linarith only [direction.2,sn]
    · have direction := cone E R t profile elbow right.origin (-q.c) (-q.s)
        (by simpa only [neg_sq] using q.unit_normal) (reverse _ _ backward)
      linarith only [direction.1,cp]
  have noReverseV (q : OpenSquare) (sn : q.s≤0)
      (sep : upper R (-q.s) q.c≤lower E (-q.s) q.c) : False := by
    have opposite : upper E q.s (-q.c)≤lower R q.s (-q.c) := by
      simpa only [neg_neg] using reverse _ _ sep
    have direction := cone E R t profile elbow right.origin q.s (-q.c)
      (by nlinarith only [q.unit_normal]) opposite
    linarith only [direction.1,sn]
  have es : E.s≤0 := by rw [profile.signed]; linarith only [profile.sinePositive]
  have axes := CongruentSAT.faceSeparation_of_disjoint E R same apart
  change pairRadius E R≤|E.c*(centerX R-centerX E)+E.s*(centerY R-centerY E)| ∨
    pairRadius E R≤|-E.s*(centerX R-centerX E)+E.c*(centerY R-centerY E)| ∨
    pairRadius R E≤|R.c*(centerX R-centerX E)+R.s*(centerY R-centerY E)| ∨
    pairRadius R E≤|-R.s*(centerX R-centerX E)+R.c*(centerY R-centerY E)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius E nx ny+supportRadius R nx ny=radius)
      (axis : radius≤|nx*(centerX R-centerX E)+ny*(centerY R-centerY E)|) :=
    separated E R nx ny (by rwa [eq])
  rcases axes with eu | ev | ru | rv
  · exact False.elim (noU E profile.cosinePositive es
      (separate _ _ _ (parallel_radius E R) eu))
  · rcases separate _ _ _ (transverse_radius E R) ev with forward | backward
    · exact Or.inl forward
    · exact False.elim (noReverseV E es backward)
  · have radius : supportRadius E R.c R.s+supportRadius R R.c R.s=pairRadius R E := by
      rw [add_comm]
      exact parallel_radius R E
    exact False.elim (noU R right.cosinePositive right.sineNonpositive
      (separate _ _ _ radius ru))
  · have radius : supportRadius E (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R E := by
      rw [add_comm]
      exact transverse_radius R E
    rcases separate _ _ _ radius rv with forward | backward
    · exact Or.inr forward
    · exact False.elim (noReverseV R right.sineNonpositive backward)

#print axioms southeast_vertex
#print axioms separators
end N12Compact.Completion.OtherCases.C983.NegativeRightSeparation
