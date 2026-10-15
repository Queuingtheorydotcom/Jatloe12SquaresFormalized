import Compact.Completion.C1092.MPPMMissingBoundaryShallowScalars
import Compact.Completion.C981.SupportForms
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! Literal actual-square inputs, simultaneous boundary faces and complete
separating-axis reduction for MISSING-BOUNDARY-SHALLOW-ANGLE, sections 1--3.
The bottom wall is a hypothesis on the whole actual B; its vertex limit
is proved here. No central-angle ceiling or boundary-center cap is used. -/
namespace N12Compact.C1092MPPMMissingBoundaryShallow
open S12 S12Pilot C977CornerCubic FourSquareAnchors ThreeSquare ABTransverse
open C977ChainBridge
set_option Elab.async false
noncomputable section

structure Input (C B : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=B.side
  centralNormal : Normal C.c C.s
  centralPositive : 0<C.s
  boundaryNormal : Normal B.c (-B.s)
  boundaryNegative : 0< -B.s
  ordinaryG : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  lowerU : -C.c-C.s/2≤C.loU
  upperU : C.loU+C.side≤0
  upperV : C.loV+C.side≤C.s
  marker : B.Inside 0 (-543/500)
  auxiliary : B.Inside (-13/50) (-1)
  origin : ¬B.Inside 0 (-1)
  cornerMarker : ¬B.Inside (-1) (-543/500)
  floor : ∀ x y,B.Inside x y → -2≤y
  apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

structure BoundaryFaces (B : OpenSquare) : Prop where
  upperV : B.loV+B.side≤-B.c
  lowerU : -B.c-(543/500)*B.s≤B.loU
  wall : (-B.s)*(B.loU+B.side)-B.c*(B.loV+B.side)≤2-B.side*B.c

/-- Both omissions and the real floor constrain the same two B faces. -/
theorem boundary_faces (C B : OpenSquare) (h : Input C B) : BoundaryFaces B := by
  have cb := strict_bounds h.boundaryNormal h.boundaryNegative
  have bp : 0<B.c := by linarith only [cb.1]
  have rp := h.boundaryNegative
  have side : 1<B.side := by rw [←h.same]; exact h.side
  have d : B.loV+B.side≤-B.c := by
    apply le_of_not_gt
    intro high
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.auxiliary.1,h.marker.2.1,h.marker.2.2.1,high,bp,rp]
  have lowV : B.loV< B.s-(543/500)*B.c := by
    apply lt_of_not_ge
    intro no
    nlinarith only [no,d,side,cb.2.1,cb.2.2.1]
  have l : -B.c-(543/500)*B.s≤B.loU := by
    apply le_of_not_gt
    intro low
    apply h.cornerMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [low,lowV,h.marker.2.1,h.marker.2.2.2,bp,rp]
  have endpoint : 0≤2+B.s*(B.loU+B.side)+B.c*B.loV := by
    apply affine_endpoint_nonnegative B.side (B.c-B.s) _ B.side_pos
    intro t positive small
    let u := B.loU+B.side-t
    let v := B.loV+t
    have own : B.Inside (B.c*u-B.s*v) (B.s*u+B.c*v) := by
      apply (inside_iff_rotated_box B _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp only [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := h.floor _ _ own
    dsimp only [u,v] at bound
    nlinarith only [bound]
  exact ⟨d,l,by nlinarith only [endpoint]⟩

/-- The two strict anchor pairs orient every real separating normal
from B toward C. Both inequalities remain strict at weak contact. -/
theorem cone (C B : OpenSquare) (h : Input C B) (nx ny : ℝ)
    (unit : nx^2+ny^2=1) (sep : upper B nx ny≤lower C nx ny) :
    0<ny ∧ nx<(30/37)*ny := by
  have b := (ABTransverse.strict_bounds B _ _ nx ny unit h.auxiliary).2
  have t := (ABTransverse.strict_bounds C _ _ nx ny unit h.forward).1
  have g := (ABTransverse.strict_bounds C _ _ nx ny unit h.ordinaryG).1
  constructor <;> linarith only [b,t,g,sep]

/-- All four signed axes of both actual squares are retained before
the strict cone removes the impossible ones. The survivors are C-v,
B-negative-u, and B-v, in that order. -/
theorem separators (C B : OpenSquare) (h : Input C B) :
    upper B (-C.s) C.c≤lower C (-C.s) C.c ∨
      upper B (-B.c) (-B.s)≤lower C (-B.c) (-B.s) ∨
      upper B (-B.s) B.c≤lower C (-B.s) B.c := by
  have cb := strict_bounds h.centralNormal h.centralPositive
  have bb := strict_bounds h.boundaryNormal h.boundaryNegative
  have cp : 0<C.c := by linarith only [cb.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have reverse (nx ny : ℝ) (sep : upper C nx ny≤lower B nx ny) :
      upper B (-nx) (-ny)≤lower C (-nx) (-ny) := by
    rw [Completion.OtherCases.WallProfile.upper_neg,
      Completion.OtherCases.WallProfile.lower_neg]
    linarith only [sep]
  have downward (nx ny : ℝ) (unit : nx^2+ny^2=1) (yn : ny≤0)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have direction := cone C B h nx ny unit sep
    linarith only [direction.1,yn]
  have axes := CongruentSAT.faceSeparation_of_disjoint B C h.same.symm
    (fun x y own => h.apart x y ⟨own.2,own.1⟩)
  change pairRadius B C≤|B.c*(centerX C-centerX B)+B.s*(centerY C-centerY B)| ∨
    pairRadius B C≤|-B.s*(centerX C-centerX B)+B.c*(centerY C-centerY B)| ∨
    pairRadius C B≤|C.c*(centerX C-centerX B)+C.s*(centerY C-centerY B)| ∨
    pairRadius C B≤|-C.s*(centerX C-centerX B)+C.c*(centerY C-centerY B)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius B nx ny+supportRadius C nx ny=radius)
      (axis : radius≤|nx*(centerX C-centerX B)+ny*(centerY C-centerY B)|) :=
    separated B C nx ny (by rwa [eq])
  rcases axes with bu | bv | cu | cv
  · rcases separate _ _ _ (parallel_radius B C) bu with forward | backward
    · exact False.elim (downward B.c B.s B.unit_normal
        (by linarith only [h.boundaryNegative]) forward)
    · exact Or.inr (Or.inl (reverse _ _ backward))
  · rcases separate _ _ _ (transverse_radius B C) bv with forward | backward
    · exact Or.inr (Or.inr forward)
    · have opposite : upper B B.s (-B.c)≤lower C B.s (-B.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      exact False.elim (downward B.s (-B.c) (by nlinarith only [B.unit_normal])
        (by linarith only [bp]) opposite)
  · have radius : supportRadius B C.c C.s+supportRadius C C.c C.s=pairRadius C B := by
      rw [add_comm]
      exact parallel_radius C B
    rcases separate _ _ _ radius cu with forward | backward
    · have direction := cone C B h C.c C.s C.unit_normal forward
      exact False.elim (by linarith only [direction.2,h.centralNormal.2.1,cp])
    · exact False.elim (downward (-C.c) (-C.s)
        (by simpa only [neg_sq] using C.unit_normal)
        (by linarith only [h.centralPositive]) (reverse _ _ backward))
  · have radius : supportRadius B (-C.s) C.c+supportRadius C (-C.s) C.c=pairRadius C B := by
      rw [add_comm]
      exact transverse_radius C B
    rcases separate _ _ _ radius cv with forward | backward
    · exact Or.inl forward
    · have opposite : upper B C.s (-C.c)≤lower C C.s (-C.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      exact False.elim (downward C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by linarith only [cp]) opposite)

end
end N12Compact.C1092MPPMMissingBoundaryShallow
