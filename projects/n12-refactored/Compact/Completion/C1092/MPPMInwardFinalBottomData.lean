import Compact.Completion.C1092.MPPMInwardFinalBottomScalars
import Compact.Completion.C1092.TwoFifthsSupport
import Compact.Completion.C1092.ShallowBoundarySupport
import Compact.Geometry.ClosedFrames

/-! The literal actual-square inputs and exhaustive normal reduction
of INWARD-BOTTOM-ANGLE. Weak walls and center signs remain weak.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal.BottomAngle
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

structure Input (C B : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=B.side
  normal : Normal C.c (-C.s)
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  forward : C.Inside (-13/50) 0
  crosspoint : C.Inside (-1/2) 0
  sharp : C.Inside (-1/100) (-27/50)
  origin : ¬C.Inside 0 0
  outer : ¬C.Inside (-1) (-2/5)
  bottomMarker : B.Inside 0 (-543/500)
  bottomNear : B.Inside (-13/50) (-1)
  bottomFar : B.Inside (-14/25) (-1)
  wall : ∀ x y,B.Inside x y → -2≤y
  center : centerX B≤0
  apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

structure CentralFaces (C : OpenSquare) : Prop where
  negative : C.s<0
  upperV : C.loV+C.side≤0
  lowerU : -C.c-(2/5)*C.s≤C.loU
  upperLowU : C.loU< -C.c/2

theorem central_faces (C B : OpenSquare) (h : Input C B) : CentralFaces C := by
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have negative : C.s<0 := by
    apply lt_of_not_ge
    intro no
    have zero : C.s=0 := by linarith only [no,h.normal.1]
    have ownI := h.inner
    have ownJ := h.forward
    simp only [OpenSquare.Inside,InBands,zero,zero_mul,mul_zero,add_zero,neg_zero] at ownI ownJ
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [ownJ.1,ownI.2.1,ownI.2.2.1,ownJ.2.2.2,cp]
  have upperV : C.loV+C.side≤0 := by
    apply le_of_not_gt
    intro high
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.forward.1,h.inner.2.1,h.marker.2.2.1,high,cp,h.normal.2.1,negative]
  have projection : -C.s+(2/5)*C.c<1 := by
    have product := mul_nonneg (show 0≤C.c+C.s by linarith only [h.normal.2.1])
      (show 0≤41*C.c-C.s by linarith only [cp,negative])
    nlinarith only [product,C.unit_normal,sq_nonneg (-C.s+(2/5)*C.c-1)]
  have lowerU : -C.c-(2/5)*C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    have lowV : C.loV<C.s-(2/5)*C.c := by
      linarith only [upperV,h.side,projection]
    apply h.outer
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,lowV,h.marker.2.1,h.marker.2.2.2,cp,h.normal.2.1,negative]
  exact ⟨negative,upperV,lowerU,by linarith only [h.crosspoint.1]⟩

theorem cone (C B : OpenSquare) (h : Input C B) (nx ny : ℝ)
    (unit : nx^2+ny^2=1) (sep : upper B nx ny≤lower C nx ny) :
    0<ny ∧ 0<(11/20)*nx+(23/50)*ny := by
  have first := (strict_bounds B _ _ nx ny unit h.bottomMarker).2
  have last := (strict_bounds C _ _ nx ny unit h.inner).1
  have far := (strict_bounds B _ _ nx ny unit h.bottomFar).2
  have sharp := (strict_bounds C _ _ nx ny unit h.sharp).1
  constructor <;> linarith only [first,last,far,sharp,sep]

theorem separators (C B : OpenSquare) (h : Input C B) (canonical : |B.s|≤B.c) :
    upper B (-C.s) C.c≤C.loV ∨
      B.loU+B.side≤lower C B.c B.s ∨
      B.loV+B.side≤lower C (-B.s) B.c := by
  have cb := normal_bounds h.normal
  have bp : 0<B.c := by
    have pos : 0≤B.c := le_trans (abs_nonneg B.s) canonical
    nlinarith only [pos,canonical,B.unit_normal,sq_abs B.s]
  have cp : 0<C.c := by linarith only [cb.1]
  have downward (nx ny : ℝ) (unit : nx^2+ny^2=1) (yn : ny≤0)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have direction := cone C B h nx ny unit sep
    linarith only [direction.1,yn]
  have backward (Q : OpenSquare) (qp : 0<Q.c) (canonicalQ : |Q.s|≤Q.c)
      (sep : upper B (-Q.c) (-Q.s)≤lower C (-Q.c) (-Q.s)) : False := by
    have direction := cone C B h (-Q.c) (-Q.s) (by nlinarith only [Q.unit_normal]) sep
    have bound := (abs_le.mp canonicalQ).1
    linarith only [direction.2,bound,qp]
  have axes := CongruentSAT.faceSeparation_of_disjoint B C h.same.symm
    (fun x y own => h.apart x y ⟨own.2,own.1⟩)
  change pairRadius B C≤|B.c*(centerX C-centerX B)+B.s*(centerY C-centerY B)| ∨
    pairRadius B C≤|-B.s*(centerX C-centerX B)+B.c*(centerY C-centerY B)| ∨
    pairRadius C B≤|C.c*(centerX C-centerX B)+C.s*(centerY C-centerY B)| ∨
    pairRadius C B≤|-C.s*(centerX C-centerX B)+C.c*(centerY C-centerY B)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius B nx ny+supportRadius C nx ny=radius)
      (axis : radius≤|nx*(centerX C-centerX B)+ny*(centerY C-centerY B)|) :=
    separated B C nx ny (by rwa [eq])
  rcases axes with bu|bv|cu|cv
  · rcases split _ _ _ (parallel_radius B C) bu with direct|back
    · exact Or.inr (Or.inl (by simpa only [(ownU B).2] using direct))
    · exact False.elim (backward B bp canonical (reverse B C _ _ back))
  · rcases split _ _ _ (transverse_radius B C) bv with direct|back
    · exact Or.inr (Or.inr (by simpa only [(ownV B).2] using direct))
    · have opposite : upper B B.s (-B.c)≤lower C B.s (-B.c) := by
        simpa only [neg_neg] using reverse B C _ _ back
      exact False.elim (downward _ _ (by nlinarith only [B.unit_normal]) (by linarith only [bp]) opposite)
  · have radius : supportRadius B C.c C.s+supportRadius C C.c C.s=pairRadius C B := by
      rw [add_comm]; exact parallel_radius C B
    rcases split _ _ _ radius cu with direct|back
    · exact False.elim (downward _ _ C.unit_normal (by linarith only [h.normal.1]) direct)
    · have canonicalC : |C.s|≤C.c := by
        rw [abs_of_nonpos (show C.s≤0 by linarith only [h.normal.1])]
        exact h.normal.2.1
      exact False.elim (backward C cp canonicalC (reverse B C _ _ back))
  · have radius : supportRadius B (-C.s) C.c+supportRadius C (-C.s) C.c=pairRadius C B := by
      rw [add_comm]; exact transverse_radius C B
    rcases split _ _ _ radius cv with direct|back
    · exact Or.inl (by simpa only [(ownV C).1] using direct)
    · have opposite : upper B C.s (-C.c)≤lower C C.s (-C.c) := by
        simpa only [neg_neg] using reverse B C _ _ back
      exact False.elim (downward _ _ (by nlinarith only [C.unit_normal]) (by linarith only [cp]) opposite)

theorem positive_wall (C B : OpenSquare) (h : Input C B) (bn : Normal B.c B.s) :
    -2*B.c+(C.side/2)*(1+B.c*(B.c+B.s))≤B.loV+B.side := by
  have bb := normal_bounds bn
  have bound := C1092ShallowBoundarySupport.bottom_center B h.wall
  simp only [C1092ShallowBoundarySupport.width0,
    abs_of_nonneg (show 0≤B.c by linarith only [bb.1]),abs_of_nonneg bn.1] at bound
  have vertical := mul_le_mul_of_nonneg_left bound (show 0≤B.c by linarith only [bb.1])
  have horizontal := mul_nonpos_of_nonneg_of_nonpos bn.1 h.center
  have coordinate := (center_coordinates B).2
  rw [←h.same] at coordinate vertical
  nlinarith only [coordinate,vertical,horizontal]

theorem negative_wall_height (C B : OpenSquare) (h : Input C B) (bn : Normal B.c (-B.s)) :
    -1<B.loV+B.side := by
  have bb := normal_bounds bn
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
    have bound := h.wall _ _ own
    dsimp only [u,v] at bound
    nlinarith only [bound]
  have marker := mul_nonneg bn.1
    (show 0≤B.loU+B.side+(543/500)*B.s by linarith only [h.bottomMarker.2.1])
  apply negative_height bn (by simpa only [←h.same] using h.side)
    (by linarith only [h.bottomMarker.2.2.2])
  nlinarith only [endpoint,marker]

#print axioms central_faces
#print axioms separators
#print axioms positive_wall
#print axioms negative_wall_height
end N12Compact.C1092MPPMInwardFinal.BottomAngle
