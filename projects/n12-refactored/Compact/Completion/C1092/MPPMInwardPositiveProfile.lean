import Compact.Completion.C1092.MPPMActualNonordinaryScalars
import Compact.Completion.C1092.MPPMInwardFinalBottomData

/-! POSITIVE-MISSING-INWARD-SUCCESSOR section 1. These simultaneous
faces belong to the same actual inward square. The strict lower
halfpoint comes from its sharp tip, independently of the omitted origin.
No successor sign or opposite-owner classification is used here. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

structure Input (C : OpenSquare) : Prop where
  side : 1<C.side
  normal : Normal C.c C.s
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  forward : C.Inside (-13/50) 0
  crosspoint : C.Inside (-1/2) 0
  sharp : C.Inside (-1/100) (-27/50)
  origin : ¬C.Inside 0 0
  outer : ¬C.Inside (-1) (-2/5)
  bottom : ¬C.Inside (-2/5) (-1)
  northwest : ¬C.Inside (-7/20) (7/20)

structure Profile (C : OpenSquare) : Prop where
  positive : 0<C.s
  lowerU : -C.c-(2/5)*C.s≤C.loU
  upperU : C.loU+C.side≤0
  lowerV : (2/5)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤(7/20)*(C.c+C.s)
  halfpoint : C.Inside 0 (-1/2)
  halfSmall : half C.c C.s<2/5
  strictOrder : C.s<C.c

/-- The canonical short direction is essential: its full-circle norm
would exceed one. The second short direction has squared norm .985. -/
theorem short_projections {c s : ℝ} (cn : Normal c s) :
    (2/5)*c+s<1 ∧ (13/20)*c+(3/4)*s<1 := by
  have cb := normal_bounds cn
  have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤41*c+s by linarith only [cb.1,cn.1])
  constructor
  · nlinarith only [product,cn.2.2,sq_nonneg ((2/5)*c+s-1)]
  · nlinarith only [cn.2.2,sq_nonneg ((3/4)*c-(13/20)*s),
      sq_nonneg ((13/20)*c+(3/4)*s-1)]

theorem half_of_width {c s α : ℝ} (cn : Normal c s) (width : 1<c+α*s) :
    half c s<α := by
  have identity := C1092MPPMInwardFinal.BottomAngle.half_identity cn
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg cn.1 (sub_nonneg.mpr high)
  nlinarith only [identity,product,width]

theorem sine_le_twice_half {c s : ℝ} (cn : Normal c s) : s≤2*half c s := by
  have data := quarter_data c s (by linarith only [(normal_bounds cn).1]) cn.1 cn.2.2
  have product := mul_nonneg cn.1 (sq_nonneg (half c s))
  nlinarith only [data.2.2.2.2,product]

theorem profile (C : OpenSquare) (h : Input C) : Profile C := by
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have sn := h.normal.1
  have order := h.normal.2.1
  have sp : 0<C.s := by
    apply lt_of_not_ge
    intro no
    have zero : C.s=0 := by linarith only [no,sn]
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [h.inner.1,h.inner.2.1,h.inner.2.2.1,h.inner.2.2.2,
        h.forward.1,h.forward.2.1,h.forward.2.2.1,h.forward.2.2.2,zero]
  have upperU : C.loU+C.side≤0 := by
    apply le_of_not_gt
    intro high
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.marker.1,h.inner.2.2.1,h.forward.2.2.2,cp,sp]
  have halfpoint : C.Inside 0 (-1/2) := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.sharp.1,h.sharp.2.2.1,h.inner.2.1,h.inner.2.2.2,cp,sp,order]
  have short := short_projections h.normal
  have sum := C1092MPPMActualNonordinary.normal_sum C.c C.s h.normal
  have lowerV : (2/5)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply h.bottom
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,upperU,h.side,h.marker.2.1,h.marker.2.2.2,short.1,cp,sp,order]
  have lowerU : -C.c-(2/5)*C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    apply h.outer
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.marker.2.1,h.sharp.2.2.1,lowerV,h.side,sum.2.1,cp,sp]
  have upperV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro high
    apply h.northwest
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.crosspoint.1,h.marker.2.2.1,lowerU,h.side,short.2,cp,sp]
  have width : 1<C.c+(2/5)*C.s := by linarith only [h.side,lowerU,upperU]
  have data := quarter_data C.c C.s cp.le sn C.unit_normal
  let x := half C.c C.s
  have relation : C.s*x=1-C.c := by
    have identity : (1+C.c)*(C.s*x-(1-C.c))=0 := by
      linear_combination C.s*data.2.2.1+C.unit_normal
    exact sub_eq_zero.mp ((mul_eq_zero.mp identity).resolve_left (by linarith only [cp]))
  have halfSmall : x<2/5 := by
    apply lt_of_not_ge
    intro high
    have product := mul_nonneg sn (show 0≤x-2/5 by linarith only [high])
    nlinarith only [product,relation,width]
  have strictOrder : C.s<C.c := by
    apply lt_of_not_ge
    intro reverse
    have equal : C.s=C.c := le_antisymm order reverse
    linarith only [width,short.1,equal]
  exact ⟨sp,lowerU,upperU,lowerV,upperV,halfpoint,halfSmall,strictOrder⟩

end
#print axioms profile
end N12Compact.C1092MPPMInwardPositive
