import Compact.Completion.C1092.MPPMNegativeRecipientWallScalars
import Compact.Completion.C1092.MPPMMissingBoundaryShallowGeometry
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareData
import Compact.Completion.C1092.TwoFifthsSupport

/-! NEGATIVE-MISSING-POSITIVE-ENDING Theorem 1, for the two actual
physical squares. A negative recipient strictly owning the disputed
origin forces the same negative boundary beyond slope 1/4. Its real
floor and both omitted points constrain the same two boundary faces.
Every signed actual normal and every weak contact is retained.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeRecipientWall
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge C977CornerCubic
open C1092WholeSupports C1092TwoFifths.Support
set_option Elab.async false
noncomputable section

structure Input (E B : OpenSquare) : Prop where
  side : 1<E.side
  same : E.side=B.side
  recipient : Normal E.c (-E.s)
  boundary : Normal B.c (-B.s)
  boundaryNegative : 0< -B.s
  originE : E.Inside 0 (-1)
  lowerU : -(13/50)*E.s≤E.loU
  upperV : E.loV+E.side≤-E.s-(14/25)*E.c
  bounds : 7/10<E.c ∧ E.c<33/40 ∧ 283/500< -E.s ∧ -E.s<71/100 ∧
    139/100<E.c-E.s
  markerB : B.Inside 0 (-543/500)
  auxiliaryB : B.Inside (-13/50) (-1)
  cornerMarkerB : ¬B.Inside (-1) (-543/500)
  floor : ∀ x y,B.Inside x y→-2≤y
  apart : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)

theorem boundary_faces (E B : OpenSquare) (h : Input E B) :
    C1092MPPMMissingBoundaryShallow.BoundaryFaces B := by
  have cb := C1092MPPMMissingBoundaryShallow.strict_bounds h.boundary h.boundaryNegative
  have bp : 0<B.c := by linarith only [cb.1]
  have rp := h.boundaryNegative
  have side : 1<B.side := by rw [←h.same]; exact h.side
  have origin : ¬B.Inside 0 (-1) := fun own => h.apart _ _ ⟨own,h.originE⟩
  have d : B.loV+B.side≤-B.c := by
    apply le_of_not_gt
    intro high
    apply origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.auxiliaryB.1,h.markerB.2.1,h.markerB.2.2.1,high,bp,rp]
  have lowV : B.loV<B.s-(543/500)*B.c := by
    apply lt_of_not_ge
    intro no
    nlinarith only [no,d,side,cb.2.1,cb.2.2.1]
  have l : -B.c-(543/500)*B.s≤B.loU := by
    apply le_of_not_gt
    intro low
    apply h.cornerMarkerB
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [low,lowV,h.markerB.2.1,h.markerB.2.2.2,bp,rp]
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

private theorem sources (E B : OpenSquare) (h : Input E B) :
    upper B (-E.s) E.c≤E.loV ∨ upper B (-B.s) B.c≤lower E (-B.s) B.c := by
  have eb := normal_bounds h.recipient
  have bb := normal_bounds h.boundary
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower E nx ny) : 0<nx ∧ 0<ny := by
    have point := (strict_bounds E _ _ nx ny unit h.originE).1
    have first := (strict_bounds B _ _ nx ny unit h.auxiliaryB).2
    have last := (strict_bounds B _ _ nx ny unit h.markerB).2
    constructor <;> linarith only [point,first,last,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes B E h.same.symm h.apart
      with a|b|c|d|e|f|g|j
  · have no := (cone _ _ B.unit_normal a).2
    exact False.elim (by linarith only [no,h.boundaryNegative])
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) b).1
    exact False.elim (by linarith only [no,bb.1])
  · exact Or.inr c
  · have no := (cone _ _ (by nlinarith only [B.unit_normal]) d).1
    exact False.elim (by linarith only [no,h.boundaryNegative])
  · have no := (cone _ _ E.unit_normal e).2
    exact False.elim (by linarith only [no,h.recipient.1])
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) f).1
    exact False.elim (by linarith only [no,eb.1])
  · exact Or.inl (by simpa only [(ownV E).1] using g)
  · have no := (cone _ _ (by nlinarith only [E.unit_normal]) j).1
    exact False.elim (by linarith only [no,h.recipient.1])

theorem steep (E B : OpenSquare) (h : Input E B) : B.c<4*(-B.s) := by
  apply lt_of_not_ge
  intro bad
  let d := E.c
  let t := -E.s
  let b := B.c
  let r := -B.s
  let k := d*b+t*r
  let delta := t*b-d*r
  have eb := normal_bounds h.recipient
  have bb := normal_bounds h.boundary
  have dp : 0<d := by dsimp [d]; linarith only [eb.1]
  have tp : 0<t := by dsimp [t]; linarith only [h.bounds.2.2.1]
  have bp : 0<b := by dsimp [b]; linarith only [bb.1]
  have rp : 0<r := h.boundaryNegative
  have slope : 4*r≤b := bad
  have relative : 2*d<3*t := by dsimp [d,t]; linarith only [h.bounds.2.1,h.bounds.2.2.1]
  have kp : 0<k := add_pos (mul_pos dp bp) (mul_pos tp rp)
  have deltap : 0<delta := by
    have first := mul_pos bp (show 0<3*t-2*d by linarith only [relative])
    have last := mul_nonneg dp.le (show 0≤b-4*r by linarith only [slope])
    have positive := mul_pos dp bp
    dsimp [delta]
    nlinarith only [first,last,positive]
  have bf := boundary_faces E B h
  rcases sources E B h with recipient|boundary
  · have formula := upper_pos_pos B t d delta k
      (by dsimp [delta,d,t,b,r]; ring) (by dsimp [k,d,t,b,r]; ring) deltap.le kp.le
    have norm : delta*b+k*r=t := by
      dsimp [delta,k,b,r]
      linear_combination t*B.unit_normal
    have identity : b*upper B t d=
        k*(b*(B.loV+B.side)-r*(B.loU+B.side))+t*(B.loU+B.side) := by
      rw [formula]
      linear_combination (B.loU+B.side)*norm
    have lowerJ : E.side-b+(543/500)*r≤B.loU+B.side := by
      dsimp [b,r]
      linarith only [bf.lowerU,h.same]
    have wallWeight := mul_le_mul_of_nonneg_left bf.wall kp.le
    have lowerWeight := mul_le_mul_of_nonneg_left lowerJ tp.le
    rw [←h.same] at wallWeight lowerWeight identity
    have comparison : E.side*(b*k+t)-2*k-b*t+(543/500)*t*r≤b*upper B t d := by
      nlinarith only [wallWeight,lowerWeight,identity]
    have margin := Scalars.upward_margin h.recipient h.boundary rp slope relative.le
    change 0<b*k+t-2*k-b*t+(543/500)*t*r+b*d at margin
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<b*k+t by positivity)
    have origin : E.loV< -d := by dsimp [d]; linarith only [h.originE.2.2.1]
    have support := mul_le_mul_of_nonneg_left recipient bp.le
    have own := mul_lt_mul_of_pos_left origin bp
    nlinarith only [comparison,margin,strict,support,own]
  · have formula := lower_np E r b (-delta) k
      (by dsimp [delta,d,t,b,r]; ring) (by dsimp [k,d,t,b,r]; ring)
      (neg_nonpos.mpr deltap.le) kp.le
    have first : delta*((13/50)*t)≤delta*E.loU :=
      mul_le_mul_of_nonneg_left (by simpa only [t, mul_neg, neg_mul] using h.lowerU) deltap.le
    have last : k*(E.loV+E.side)≤k*(t-(14/25)*d) :=
      mul_le_mul_of_nonneg_left h.upperV kp.le
    have margin := Scalars.boundary_margin h.recipient h.boundary rp slope
      h.bounds.2.1 h.bounds.2.2.1 h.bounds.2.2.2.1 h.bounds.2.2.2.2
    change 0<k+delta-(543/500)*b+(13/50)*delta*t-k*(t-(14/25)*d) at margin
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<k+delta by linarith only [kp,deltap])
    have marker : -(543/500)*b<B.loV+B.side := by
      dsimp [b]; linarith only [h.markerB.2.2.2]
    rw [(ownV B).2] at boundary
    change B.loV+B.side≤lower E r b at boundary
    nlinarith only [formula,first,last,margin,strict,marker,boundary]

end
#print axioms boundary_faces
#print axioms steep
end N12Compact.C1092MPPMNegativeRecipientWall
