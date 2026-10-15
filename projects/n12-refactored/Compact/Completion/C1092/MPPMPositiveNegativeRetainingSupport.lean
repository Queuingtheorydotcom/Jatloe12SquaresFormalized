import Compact.Completion.C1092.MPPMPositiveNegativeRetainingScalars
import Compact.Completion.C1092.MPPMNonpositivePredecessor
import Compact.Completion.C1092.MPPMAllNonpositiveCore

/-! Complete signed-axis comparison for a positive source and a retaining
nonpositive physical successor. All positions below are faces of the same
actual squares. The bar belongs to a third actual square. Source only. -/
namespace N12Compact.C1092MPPMPositiveNegativeRetaining
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open Completion.OtherCases C1092MPPMOrdinaryNegativeHalfpoint
set_option Elab.async false
noncomputable section

structure Input (C E R : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  sourceNormal : Normal C.c C.s
  targetNormal : Normal E.c (-E.s)
  sourceMarker : C.Inside (-7/20) (-7/20)
  lowerU : -C.c-C.s≤C.loU
  upperV : C.loV+C.side≤C.s
  targetMarker : E.Inside (7/20) (-7/20)
  ordinary : E.Inside (13/50) (-1)
  outer : E.Inside (2/5) (-1)
  forward : E.Inside 0 (-13/50)
  faces : C1092MPPMAllNonpositive.SuccessorFaces E
  missing : ¬E.Inside (1/2) 0
  apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)
  bar : ∀ y, -(14/25)≤y → y≤0 → R.Inside 1 y

structure Profile (E : OpenSquare) : Prop where
  negative : 0< -E.s
  slope : (-E.s)/E.c<1/4
  height : -E.loU<43/500
  cosine : 97/100<E.c
  sine : -E.s<1/4

theorem negative (C E R : OpenSquare) (h : Input C E R) : 0< -E.s := by
  linarith only [h.faces.lowerV,h.ordinary.2.2.1]

/-- The genuine omitted next crosspoint can leave only through the
successor's upper physical second face, including equality. -/
theorem next_face (C E R : OpenSquare) (h : Input C E R) :
    E.loV+E.side≤-E.s/2 := by
  have eb := normal_bounds h.targetNormal
  have dp : 0<E.c := by linarith only [eb.1]
  have tn := h.targetNormal.1
  have order := h.targetNormal.2.1
  apply le_of_not_gt
  intro high
  apply h.missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.forward.1,dp,order]
  · linarith only [h.faces.lowerU,h.side,h.same,eb.2.1,tn]
  · linarith only [h.ordinary.2.2.1,dp,tn]
  · linarith only [high]

/-- The first two normals cannot separate. The remaining recipient
normal bounds the actual native height H=-E.loU. -/
theorem height_envelope (C E R : OpenSquare) (h : Input C E R) :
    -E.loU<(43/500)*E.c+E.s/2 := by
  let c := C.c
  let s := C.s
  let d := E.c
  let t := -E.s
  let k := c*d-s*t
  let l := c*t+s*d
  have cn : Normal c s := h.sourceNormal
  have en : Normal d t := h.targetNormal
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cf : Frame c s := ⟨by linarith only [cb.1],cn.1,cn.2.1,cn.2.2⟩
  have ef : Frame d t := ⟨by linarith only [eb.1],en.1,en.2.1,en.2.2⟩
  have tp : 0<t := negative C E R h
  have kn : 0≤k := (C1092MPPMNonpositivePredecessor.relative c s d t cf ef).1
  have ln : 0≤l := (C1092MPPMNonpositivePredecessor.relative c s d t cf ef).2
  have lh : l≤1 := by
    dsimp [l]
    nlinarith only [cn.2.2,en.2.2,sq_nonneg (c-t),sq_nonneg (s-d)]
  have low : E.loU<(13/50)*t := by
    dsimp [t]
    linarith only [h.forward.1]
  have high : E.loV+C.side≤t/2 := by
    dsimp [t]
    linarith only [next_face C E R h,h.same]
  have floor : C.side-d≤E.loV+C.side := by
    dsimp [d]
    linarith only [h.faces.lowerV]
  have sourceSupport : lower E C.c C.s=k*E.loU+l*E.loV :=
    C1092WholeSupports.lower_nn E C.c C.s k l
      (by dsimp [k,c,s,d,t]; ring) (by dsimp [l,c,s,d,t]; ring) kn ln
  have transverseSupport : lower E C.s (-C.c)=l*E.loU-k*(E.loV+C.side) := by
    have support := C1092WholeSupports.lower_pn E C.s (-C.c) l (-k)
      (by dsimp [l,c,s,d,t]; ring) (by dsimp [k,c,s,d,t]; ring)
      ln (neg_nonpos.mpr kn)
    simpa only [←h.same,neg_mul] using support
  have targetSupport : upper C E.c E.s=k*(C.loU+C.side)-l*C.loV := by
    have first : E.c*C.c+E.s*C.s=k := by dsimp [k,c,s,d,t]; ring
    have second : -E.c*C.s+E.s*C.c= -l := by dsimp [l,c,s,d,t]; ring
    rw [(C1092WholeSupports.formulas C E.c E.s).2,first,second,
      max_eq_left kn,max_eq_right (neg_nonpos.mpr ln)]
    ring
  have axes := C1092MPPMNonpositivePredecessor.positive_axes C E h.same cf ef
    h.sourceMarker h.targetMarker h.ordinary h.apartCE
  rcases axes with sourceAxis | transverseAxis | targetAxis
  · rw [sourceSupport] at sourceAxis
    have lowK := mul_le_mul_of_nonneg_left low.le kn
    have highL := mul_le_mul_of_nonneg_left
      (show E.loV≤t/2-C.side by linarith only [high]) ln
    have margin := Scalars.first_margin cn en tp
    have identity : C.side-c-s-k*((13/50)*t)-l*(t/2-C.side)=
        1-Scalars.P d t*c-Scalars.Q d t*s+(C.side-1)*(1+l) := by
      dsimp [Scalars.P,Scalars.Q,k,l]
      ring
    have sideMargin := mul_nonneg (sub_nonneg.mpr h.side.le)
      (show 0≤1+l by linarith only [ln])
    have lower : -c-s≤C.loU := h.lowerU
    exfalso
    nlinarith only [sourceAxis,lowK,highL,margin,identity,sideMargin,lower]
  · rw [transverseSupport] at transverseAxis
    have lowL := mul_le_mul_of_nonneg_left low.le ln
    have floorK := mul_le_mul_of_nonneg_left floor kn
    have margin := Scalars.transverse_margin cn en kn lh
    change 0<1-s+k*(1-d)-(13/50)*l*t at margin
    have identity : C.side-s-(13/50)*l*t+k*(C.side-d)=
        1-s+k*(1-d)-(13/50)*l*t+(C.side-1)*(1+k) := by ring
    have sideMargin := mul_nonneg (sub_nonneg.mpr h.side.le)
      (show 0≤1+k by linarith only [kn])
    have cap : C.loV+C.side≤s := h.upperV
    exfalso
    nlinarith only [transverseAxis,lowL,floorK,margin,identity,sideMargin,cap]
  · rw [targetSupport] at targetAxis
    have lower : C.side-c-s≤C.loU+C.side := by
      dsimp [c,s]
      linarith only [h.lowerU]
    have cap : C.loV≤s-C.side := by
      dsimp [s]
      linarith only [h.upperV]
    have weightedU := mul_le_mul_of_nonneg_left lower kn
    have weightedV := mul_le_mul_of_nonneg_left cap ln
    have identity : l*(s-C.side)-k*(C.side-c-s)=
        d*(1+c*s-c-s)-t*(c-s+s^2)-(C.side-1)*(k+l) := by
      dsimp [k,l]
      linear_combination d*cn.2.2
    have loss := mul_nonneg (sub_nonneg.mpr h.side.le) (add_nonneg kn ln)
    have margin := Scalars.envelope cn en
    have result : -E.loU<(43/500)*d-t/2 := by
      nlinarith only [targetAxis,weightedU,weightedV,identity,loss,margin]
    dsimp [d,t] at result
    linarith only [result]

end
end N12Compact.C1092MPPMPositiveNegativeRetaining
