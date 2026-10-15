import Compact.Completion.C1092.MMMP.NearCrossing
import S12.ShortCluster

/-! A true short foreign bar excludes the entire nonpositive inward
frame. The actual wall endpoint at .39 is an explicit original-owner
premise for the compact half-angle crossing argument. -/
namespace N12Compact.C1092MMMPShortBarNegative
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

theorem impossible (C W : OpenSquare) (cn : Normal C.c (-C.s))
    (side : 1<C.side) (same : C.side=W.side)
    (M : C.Inside (7/20) (7/20)) (P : C.Inside 0 (13/50))
    (Q : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (R : ¬C.Inside 1 (2/5)) (A : ¬C.Inside (13/50) 1)
    (bar : ∀ x : ℝ, 0≤x → x≤13/50 → ¬C.Inside x 1)
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (near : W.Inside 1 (39/100))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  classical
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have sn : C.s≤0 := by linarith only [cn.1]
  have lowerV : 0≤C.loV := by
    apply le_of_not_gt
    intro low
    apply O
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using
      (show C.loU<0 ∧ 0<C.loU+C.side ∧ C.loV<0 ∧ 0<C.loV+C.side by
        refine ⟨?_,?_,low,?_⟩ <;> linarith only [P.1,Q.2.1,M.2.2.2,cp,sn])
  have sp : 0< -C.s := by nlinarith only [Q.2.2.1,lowerV]
  have upperU : C.loU+C.side≤C.c+(2/5)*C.s := by
    apply le_of_not_gt
    intro upper
    apply R
    have short := short_projections C (7/10) (7/10) (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [Q.1,Q.2.2.1,upper,cn.2.1,cp,sn,lowerV,side,short.2.2.2]
  have aLowerU : C.loU<(13/50)*C.c+C.s := by
    apply lt_of_not_ge
    intro low
    have short := short_projections C (37/50) (-3/5) (by norm_num)
    linarith only [upperU,low,side,short.2.1]
  have upperV : C.loV+C.side≤C.c-(13/50)*C.s := by
    apply le_of_not_gt
    intro upper
    apply A
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [aLowerU,M.2.1,Q.2.2.1,cp,sn,upper]
  let z := (-C.s)/(1+C.c)
  have den : 0<1+C.c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have identity : (1+C.c)*(C.c-(13/50)*C.s-1)=
      (-C.s)*((13/50)*(1+C.c)+C.s) := by
    linear_combination C.unit_normal
  have product := mul_pos den
    (show 0<C.c-(13/50)*C.s-1 by linarith only [upperV,lowerV,side])
  have coefficient : 0<(13/50)*(1+C.c)+C.s := by
    apply lt_of_not_ge
    intro failure
    have bad := mul_nonpos_of_nonneg_of_nonpos sp.le failure
    linarith only [product,identity,bad]
  have small : z<13/50 := by
    dsimp [z]
    apply (div_lt_iff₀ den).mpr
    linarith only [coefficient]
  have crossing := C1092MMMPNearCrossing.point C W C.c (-C.s) rfl (by ring) cn side same
    lowerV P Q S T near wall cut apart
  exact bar z zp.le small.le crossing

#print axioms impossible
end N12Compact.C1092MMMPShortBarNegative
