import Compact.Completion.C1092.MPPMForwardPositiveDScalars
import Compact.Geometry.ClosedFrames

/-! Actual predecessor face exits in C1092-POSITIVE-D-TRANSFER section 2.
The two cap regimes are derived from literal omissions, with all weak
contacts retained. No wall or additional origin premise is used. Uncompiled. -/
namespace N12Compact.C1092MPPMForwardPositiveD
open S12 S12Pilot
set_option Elab.async false

structure Predecessor (C : OpenSquare) : Prop where
  marker : C.Inside (33/20) (33/20)
  ordinaryP : C.Inside 1 (87/50)
  ordinaryG : C.Inside 1 (8/5)
  forward : C.Inside (87/50) 2
  halfpoint : ¬C.Inside 1 (3/2)
  northwest : ¬C.Inside (33/20) (47/20)
  wallMarker : ¬C.Inside (457/500) 2
  wallF : ¬C.Inside 1 (113/50)

theorem predecessor_faces (C : OpenSquare) (side : 1<C.side)
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c) (h : Predecessor C) :
    C.c+(3/2)*C.s≤C.loU ∧ ∃ f : ℝ,C.loV+C.side≤f ∧ Coefficients C.c C.s f := by
  have cu := (CommonCases.CanonicalScalars.bounds C.c C.s cp sn order C.unit_normal).2.1
  have lower : C.c+(3/2)*C.s≤C.loU := by
    apply le_of_not_gt
    intro lowU
    have lowV : -C.s+(3/2)*C.c≤C.loV := by
      apply le_of_not_gt
      intro low
      apply h.halfpoint
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowU,low,h.ordinaryG.2.1,h.ordinaryG.2.2.2,cp,sn]
    have shallow : 13*C.s<3*C.c := by linarith only [lowV,h.marker.2.2.1]
    have upper : C.loV+C.side≤-(33/20)*C.s+(47/20)*C.c := by
      apply le_of_not_gt
      intro high
      apply h.northwest
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [high,h.ordinaryP.1,h.forward.2.1,h.marker.2.2.1,cp,sn,shallow]
    linarith only [lowV,upper,side,cu,sn]
  have cap : C.loV+C.side≤(113/50)*C.c-C.s := by
    apply le_of_not_gt
    intro high
    apply h.wallF
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinaryP.1,h.ordinaryP.2.2.1,h.forward.2.1,cp,sn,order]
  refine ⟨lower,?_⟩
  by_cases wallLower : (457/500)*C.c+2*C.s≤C.loU
  · have shallow : 200*C.s<43*C.c := by linarith only [wallLower,h.ordinaryG.1]
    exact ⟨(113/50)*C.c-C.s,cap,regime_one C.c C.s cp sn order C.unit_normal shallow⟩
  · have upper : C.loV+C.side≤2*C.c-(457/500)*C.s := by
      apply le_of_not_gt
      intro high
      apply h.wallMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [wallLower,high,h.forward.2.1,h.ordinaryG.2.2.1,cp,sn]
    exact ⟨2*C.c-(457/500)*C.s,upper,regime_two C.c C.s cp sn order C.unit_normal⟩

#print axioms predecessor_faces
end N12Compact.C1092MPPMForwardPositiveD
