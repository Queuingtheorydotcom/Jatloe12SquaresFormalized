import Compact.Completion.C1092.MPPMForwardPositiveDFaces
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! The recipient-normal comparisons in C1092-POSITIVE-D-TRANSFER
sections 4--5. Each actual support is expanded before the two relative
angle orders are split. Aligned angles are retained in both weak cases.
The single coefficient contract covers both predecessor cap regimes.
These are source proofs, not compilation receipts. -/
namespace N12Compact.C1092MPPMForwardPositiveD
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open Completion.OtherCases
set_option Elab.async false

private theorem coefficient_tilt (c s d t f : ℝ) (cp : 0<c) (dp : 0<d)
    (data : Coefficients c s f) (ordered : 0≤c*t-s*d) :
    0<coeffA c s f*t+coeffB c s f*d := by
  have first := mul_nonneg data.first ordered
  have last := mul_pos dp data.coupled
  have identity : c*(coeffA c s f*t+coeffB c s f*d)=
      coeffA c s f*(c*t-s*d)+d*(coeffA c s f*s+coeffB c s f*c) := by ring
  have positive : 0<c*(coeffA c s f*t+coeffB c s f*d) := by
    rw [identity]
    exact add_pos_of_nonneg_of_pos first last
  exact (mul_pos_iff_of_pos_left cp).mp positive

theorem recipient_u (C J : OpenSquare) (f : ℝ)
    (side : 1<C.side) (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c)
    (dp : 0<J.c) (tn : 0≤J.s)
    (lowerU : C.c+(3/2)*C.s≤C.loU) (upperV : C.loV+C.side≤f)
    (forward : C.Inside (87/50) 2) (data : Coefficients C.c C.s f) :
    2*J.c+J.s<upper C J.c J.s := by
  let K := C.c*J.c+C.s*J.s
  let D := C.c*J.s-C.s*J.c
  have kp : 0<K := by
    exact add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg sn tn)
  have cu := (CommonCases.CanonicalScalars.bounds C.c C.s cp sn order C.unit_normal).2.1
  have alpha : J.c*C.c+J.s*C.s=K := by dsimp only [K]; ring
  have beta : -J.c*C.s+J.s*C.c=D := by dsimp only [D]; ring
  by_cases dn : 0≤D
  · have support : upper C J.c J.s=K*(C.loU+C.side)+D*(C.loV+C.side) := by
      rw [WallProfile.upper_in_bands,alpha,beta,abs_of_nonneg kp.le,abs_of_nonneg dn]
      ring
    have project : K*(2*C.c+C.s)+D*(C.c-2*C.s)=2*J.c+J.s := by
      dsimp only [K,D]
      linear_combination (2*J.c+J.s)*C.unit_normal
    have first := mul_nonneg kp.le (sub_nonneg.mpr lowerU)
    have last := mul_nonneg dn (sub_nonneg.mpr forward.2.2.2.le)
    have strict := mul_pos kp (show 0<C.side-C.c+C.s/2 by linarith only [side,cu,sn])
    have margin := mul_nonneg dn (show 0≤C.c+(13/50)*C.s by linarith only [cp,sn])
    rw [support]
    dsimp only [K,D] at first last strict margin project ⊢
    nlinarith only [first,last,strict,margin,project]
  · have nonpositive : D≤0 := le_of_not_ge dn
    let L := -D
    have ln : 0≤L := neg_nonneg.mpr nonpositive
    have support : upper C J.c J.s=K*(C.loU+C.side)-L*C.loV := by
      rw [WallProfile.upper_in_bands,alpha,beta,abs_of_nonneg kp.le,abs_of_nonpos nonpositive]
      dsimp only [L]
      ring
    have identity : K*(C.c+(3/2)*C.s)-L*f+K+L-(2*J.c+J.s)=
        coeffA C.c C.s f*J.c+(37/50-coeffB C.c C.s f)*J.s := by
      dsimp only [K,L,D,coeffA,coeffB]
      ring
    have first := mul_nonneg kp.le (sub_nonneg.mpr lowerU)
    have last := mul_nonneg ln (sub_nonneg.mpr upperV)
    have strict := mul_pos (sub_pos.mpr side) (show 0<K+L by linarith only [kp,ln])
    have marginA := mul_nonneg data.first dp.le
    have marginB := mul_nonneg (sub_nonneg.mpr data.second) tn
    rw [support]
    dsimp only [K,L,D] at first last strict identity ⊢
    nlinarith only [first,last,strict,identity,marginA,marginB]

theorem recipient_negative_v (C J : OpenSquare) (f : ℝ)
    (side : 1<C.side) (cp : 0<C.c) (sn : 0≤C.s)
    (dp : 0<J.c) (tn : 0≤J.s)
    (lowerU : C.c+(3/2)*C.s≤C.loU) (upperV : C.loV+C.side≤f)
    (ordinaryG : C.Inside 1 (8/5)) (data : Coefficients C.c C.s f) :
    2*J.s-(87/50)*J.c<upper C J.s (-J.c) := by
  let K := C.c*J.c+C.s*J.s
  let D := C.c*J.s-C.s*J.c
  have kp : 0<K := add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg sn tn)
  have alpha : J.s*C.c+(-J.c)*C.s=D := by dsimp only [D]; ring
  have beta : -J.s*C.s+(-J.c)*C.c= -K := by dsimp only [K]; ring
  by_cases dn : 0≤D
  · have support : upper C J.s (-J.c)=D*(C.loU+C.side)-K*C.loV := by
      rw [WallProfile.upper_in_bands,alpha,beta,abs_of_nonneg dn,
        abs_of_nonpos (by linarith only [kp])]
      ring
    have identity : D*(C.c+(3/2)*C.s)-K*f+K+D-(2*J.s-(87/50)*J.c)=
        coeffA C.c C.s f*J.s+coeffB C.c C.s f*J.c := by
      dsimp only [K,D,coeffA,coeffB]
      ring
    have margin := coefficient_tilt C.c C.s J.c J.s f cp dp data dn
    have first := mul_nonneg dn (sub_nonneg.mpr lowerU)
    have last := mul_nonneg kp.le (sub_nonneg.mpr upperV)
    have strict := mul_pos (sub_pos.mpr side) (show 0<K+D by linarith only [kp,dn])
    rw [support]
    dsimp only [K,D] at identity first last strict ⊢
    nlinarith only [identity,first,last,strict,margin]
  · have nonpositive : D≤0 := le_of_not_ge dn
    let L := -D
    have ln : 0≤L := neg_nonneg.mpr nonpositive
    have support : upper C J.s (-J.c)= -L*C.loU-K*C.loV := by
      rw [WallProfile.upper_in_bands,alpha,beta,abs_of_nonpos nonpositive,
        abs_of_nonpos (by linarith only [kp])]
      dsimp only [L]
      ring
    have project : -L*(2*C.c+(87/50)*C.s)-K*((87/50)*C.c-2*C.s)=
        2*J.s-(87/50)*J.c := by
      dsimp only [K,L,D]
      linear_combination (2*J.s-(87/50)*J.c)*C.unit_normal
    have first := mul_nonneg ln (sub_nonneg.mpr ordinaryG.1.le)
    have last := mul_nonneg kp.le (sub_nonneg.mpr upperV)
    have strict := mul_pos kp
      (show 0<C.side+((87/50)*C.c-2*C.s)-f by linarith only [side,data.short])
    have margin := mul_nonneg ln (show 0≤C.c+(7/50)*C.s by linarith only [cp,sn])
    rw [support]
    dsimp only [K,L,D] at first last strict margin project ⊢
    nlinarith only [first,last,strict,margin,project]

#print axioms recipient_u
#print axioms recipient_negative_v
end N12Compact.C1092MPPMForwardPositiveD
