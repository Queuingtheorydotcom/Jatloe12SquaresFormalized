import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A genuine foreign strict bar gives the inward center for every
nonnegative canonical angle, including both canonical endpoints. -/
namespace N12Compact.C1092InwardBarCenter
open S12 S12Pilot
set_option Elab.async false

theorem point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (M : q.Inside (7/20) (7/20)) (P : q.Inside 0 (13/50))
    (Q : q.Inside (13/50) 0) (A : ¬ q.Inside (2/5) 1)
    (H : ¬ q.Inside (14/25) 1)
    (bar : ∀ y : ℝ, 0 ≤ y → y ≤ 39/100 → ¬ q.Inside 1 y) :
    q.Inside 0 0 := by
  classical
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have sum : 1 ≤ q.c+q.s := by
    nlinarith only [q.unit_normal,mul_nonneg cp.le sn,cp,sn]
  by_contra missing
  have lowerU : 0 ≤ q.loU := by
    apply le_of_not_gt
    intro h
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h,M.2.1,Q.2.2.1,P.2.2.2,cp,sn]
  have sp : 0 < q.s := by nlinarith only [lowerU,P.1]
  have middle : q.s+(2/5)*q.c ≤ 1 := by
    have gap := mul_nonneg (sub_nonneg.mpr order)
      (show 0 ≤ (41/50)*q.c+(1/50)*q.s by linarith only [cp,sn])
    have square : (q.s+(2/5)*q.c)^2 ≤ 49/50 := by
      nlinarith only [q.unit_normal,gap]
    nlinarith only [square,sq_nonneg (q.s+(2/5)*q.c-1)]
  have upperA : q.loV+q.side ≤ q.c-(2/5)*q.s := by
    apply le_of_not_gt
    intro h
    apply A
    exact ⟨by linarith only [M.1,cp,sn],
      by linarith only [middle,side,lowerU],
      by linarith only [Q.2.2.1,cp,order],by linarith only [h]⟩
  let z := q.s/(1+q.c)
  have denominator : 0 < 1+q.c := by linarith only [cp]
  have zp : 0 < z := div_pos sp denominator
  have angle : z*(1+q.c)=q.s := by dsimp [z]; field_simp [denominator.ne']
  have unitAngle : q.s*z=1-q.c := by
    dsimp [z]
    field_simp [denominator.ne']
    nlinarith only [q.unit_normal]
  by_cases large : 39/100 ≤ z
  · have owned : q.Inside 1 (39/100) := by
      have weight := mul_nonneg sn (sub_nonneg.mpr large)
      have slope := mul_nonneg denominator.le (sub_nonneg.mpr large)
      have chord := short_projections q (61/100) (3/5) (by norm_num)
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [Q.1,cp,sn]
      · nlinarith only [unitAngle,weight,lowerU,side]
      · linarith only [upperA,side,chord.2.1]
      · nlinarith only [P.2.2.2,slope,angle,cp]
    exact bar _ (by norm_num) (by norm_num) owned
  · have small : z ≤ 39/100 := (lt_of_not_ge large).le
    have lastBand : q.loV < -z := by
      by_cases turn : 3/5 ≤ q.s+(2/5)*q.c
      · have weight := mul_nonpos_of_nonneg_of_nonpos zp.le
          (show 3/5-q.s-(2/5)*q.c ≤ 0 by linarith only [turn])
        have identity : q.c-(2/5)*q.s+z-1=z*(3/5-q.s-(2/5)*q.c) := by
          nlinarith only [angle,unitAngle]
        nlinarith only [weight,identity,upperA,side]
      · have upperH : q.loV+q.side ≤ q.c-(14/25)*q.s := by
          apply le_of_not_gt
          intro h
          apply H
          exact ⟨by linarith only [M.1,cp,sn],
            by linarith only [turn,cu,lowerU,side],
            by linarith only [Q.2.2.1,cp,order],by linarith only [h]⟩
        have weight := mul_nonpos_of_nonneg_of_nonpos zp.le
          (show 11/25-q.s-(14/25)*q.c ≤ 0 by linarith only [sum,sn])
        have identity : q.c-(14/25)*q.s+z-1=z*(11/25-q.s-(14/25)*q.c) := by
          nlinarith only [angle,unitAngle]
        nlinarith only [weight,identity,upperH,side]
    have owned : q.Inside 1 z := by
      have uIdentity : q.c+q.s*z=1 := by linarith only [unitAngle]
      have vIdentity : -q.s+q.c*z=-z := by nlinarith only [angle]
      refine ⟨?_,?_,?_,?_⟩
      · nlinarith only [P.1,uIdentity,cu,order]
      · nlinarith only [uIdentity,side,lowerU]
      · nlinarith only [vIdentity,lastBand]
      · nlinarith only [vIdentity,P.2.2.2,zp,cp]
    exact bar z zp.le small owned

#print axioms point
end N12Compact.C1092InwardBarCenter
