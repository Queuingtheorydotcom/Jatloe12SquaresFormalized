import Compact.Completion.C1092.MPPMElbowIsolation
import Compact.Completion.C1092.MPPMElbowSuccessorScalars

/-! ELBOW-SUCCESSOR Theorem 1, for the same two actual squares.
Every nonnegative canonical successor frame is excluded by the actual
four-axis separation theorem, including zero tilt and the diagonal.
The surviving reframe preserves both its physical interior and side. -/
namespace N12Compact.C1092MPPMElbowSuccessor
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
open C1092MMMPEndingAxes C1092MPPMElbowScalars C1092MPPMElbowIsolation
open C1092MPPMElbowSuccessorScalars
set_option Elab.async false

theorem nonnegative_impossible (C E : OpenSquare)
    (side : 1<C.side) (same : C.side=E.side) (h : C1092ElbowProfile.Profile C)
    (en : Normal E.c E.s) (cM : C.Inside (-7/20) (-7/20))
    (M : E.Inside (7/20) (-7/20))
    (A : E.Inside (13/50) (-1)) (B : E.Inside (2/5) (-1))
    (G : ¬E.Inside 1 (-2/5)) (K : ¬E.Inside 1 (-1))
    (R : ¬E.Inside 0 (-543/500))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : False := by
  have eb := normal_bounds en
  have cp : 0<C.c := by linarith only [h.cosine]
  have dp : 0<E.c := by linarith only [eb.1]
  have cap : E.loU+E.side≤E.c-(2/5)*E.s := by
    apply le_of_not_gt
    intro high
    apply G
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,M.1,M.2.2.2,B.2.2.1,dp,en.1,en.2.1]
  have low : E.loU≤E.c-(2/5)*E.s-C.side := by linarith only [cap,same]
  have vHigh : E.loV≤-E.c-(2/5)*E.s := by linarith only [B.2.2.1]
  have vLow : -(7/20)*(E.c+E.s)≤E.loV+E.side := by linarith only [M.2.2.2]
  have firstFloor : C.side-C.c-(2/5)*C.s≤C.loU+C.side := by
    linarith only [h.lowerU]
  have lastFloor : C.side+(2/5)*C.s-C.c≤C.loV+C.side := by
    linarith only [h.lowerV]
  have firstCap : C.loU≤-(13/50)*C.s-C.side := by linarith only [h.upperU]
  have lastCap : C.loV≤(7/20)*(C.c+C.s)-C.side := by linarith only [h.upperV]
  let k := kappa C.c C.s E.c E.s
  let l := sigma C.c C.s E.c E.s
  have rel := frames h.normal en
  have kp : 0<k := by dsimp [k]; linarith only [rel.1]
  have sumIdentity : E.c+E.s=k*(C.c+C.s)+l*(C.c-C.s) := by
    dsimp [k,l,kappa,sigma]
    linear_combination -(E.c+E.s)*C.unit_normal
  have axes := positive_axes C E same cp h.sinePositive dp en.1 cM M apart
  rcases axes with own|transverse|neighbor|neighborV
  · by_cases order : 0≤l
    · have formula := lower_pn E C.c C.s k (-l)
        (by dsimp [k,kappa]) (by dsimp [l,sigma]; ring) kp.le (by linarith only [order])
      have first := mul_le_mul_of_nonneg_left low kp.le
      have last := mul_le_mul_of_nonneg_left vLow order
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k by linarith only [kp])
      have margin := own_after h.normal en order
      dsimp [k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [own,formula,first,last,strict,margin,firstFloor]
    · have ln : l≤0 := (lt_of_not_ge order).le
      have formula := lower_nn E C.c C.s k (-l)
        (by dsimp [k,kappa]) (by dsimp [l,sigma]; ring) kp.le (by linarith only [ln])
      have first := mul_le_mul_of_nonneg_left low kp.le
      have last := mul_le_mul_of_nonneg_left vHigh (show 0≤-l by linarith only [ln])
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k by linarith only [kp])
      have margin := own_before h.normal en ln
      dsimp [k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [own,formula,first,last,strict,margin,firstFloor]
  · have unit : C.s^2+(-C.c)^2=1 := by nlinarith only [C.unit_normal]
    have formula : upper C C.s (-C.c)= -C.loV := by
      have raw := upper_nonpositive C C.s (-C.c) 0 (-1)
        (by ring) (by nlinarith only [C.unit_normal]) (by norm_num) (by norm_num)
      simpa using raw
    have strict := (strict_bounds E _ _ C.s (-C.c) unit M).1
    nlinarith only [transverse,formula,strict,lastCap,side,h.sum]
  · by_cases order : 0≤l
    · have formula := upper_nn C E.c E.s k l
        (by dsimp [k,kappa]; ring) (by dsimp [l,sigma]; ring) kp.le order
      have first := mul_le_mul_of_nonneg_left firstFloor kp.le
      have last := mul_le_mul_of_nonneg_left lastFloor order
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k+l by linarith only [kp,order])
      have margin := second_nonnegative h.normal en order
      dsimp [F1,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [neighbor,formula,first,last,strict,margin,low]
    · have ln : l≤0 := (lt_of_not_ge order).le
      have formula := upper_pn C E.c E.s k l
        (by dsimp [k,kappa]; ring) (by dsimp [l,sigma]; ring) kp.le ln
      have first := mul_le_mul_of_nonneg_left firstFloor kp.le
      have last := mul_le_mul_of_nonpos_left lastCap ln
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k-l by linarith only [kp,ln])
      have margin := fourth_nonnegative h.normal en h.sine.le ln
      dsimp [F3,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [neighbor,formula,first,last,strict,margin,low]
  · have unit : E.s^2+(-E.c)^2=1 := by nlinarith only [E.unit_normal]
    have mark := (strict_bounds E _ _ E.s (-E.c) unit M).1
    by_cases order : 0≤l
    · have formula := upper_pn C E.s (-E.c) l (-k)
        (by dsimp [l,sigma]; ring) (by dsimp [k,kappa]; ring) order (by linarith only [kp])
      have first := mul_le_mul_of_nonneg_left firstFloor order
      have last := mul_le_mul_of_nonpos_left lastCap (show -k≤0 by linarith only [kp])
      by_cases corner : E.loU+E.side≤E.c-E.s
      · have cut : 130*E.s<43*E.c := by
          by_cases lowU : -(543/500)*E.s≤E.loU
          · apply narrow_width en
            linarith only [lowU,corner,side,same]
          · have lowV : -(543/500)*E.c≤E.loV := by
              apply le_of_not_gt
              intro lowV
              apply R
              refine ⟨?_,?_,?_,?_⟩ <;>
                linarith only [lowU,lowV,A.2.1,M.2.2.2,dp,en.1,en.2.1]
            linarith only [lowV,A.2.2.1]
        have angle := corner_angle en cut
        have margin := transverse_after_small h.normal en h.sine h.sum order angle.1 angle.2
        have strict := mul_pos (sub_pos.mpr side) (show 0<k+l by linarith only [kp,order])
        dsimp [k,l,kappa,sigma] at formula first last strict margin sumIdentity
        nlinarith only [neighborV,mark,formula,first,last,strict,margin,sumIdentity]
      · have lowV : -E.c-E.s≤E.loV := by
          apply le_of_not_gt
          intro lowV
          apply K
          refine ⟨?_,?_,?_,?_⟩ <;>
            linarith only [corner,lowV,A.1,B.2.2.2,dp,en.1]
        have lowerFormula : lower E E.s (-E.c)= -(E.loV+E.side) := by
          have du : E.s*E.c+(-E.c)*E.s=0 := by ring
          have dv : -E.s*E.s+(-E.c)*E.c= -1 := by nlinarith only [E.unit_normal]
          rw [(formulas E E.s (-E.c)).1,du,dv]
          norm_num <;> ring
        have capLower : lower E E.s (-E.c)≤E.c+E.s-C.side := by
          rw [lowerFormula]
          linarith only [lowV,same]
        have margin := transverse_corner h.normal en h.cosine h.sine
        have strict := mul_pos (sub_pos.mpr side) (show 0<1+k+l by linarith only [kp,order])
        dsimp [k,l,kappa,sigma] at formula first last strict margin sumIdentity
        nlinarith only [neighborV,formula,first,last,strict,margin,capLower,sumIdentity]
    · have ln : l≤0 := (lt_of_not_ge order).le
      have formula := upper_nonpositive C E.s (-E.c) l (-k)
        (by dsimp [l,sigma]; ring) (by dsimp [k,kappa]; ring) ln (by linarith only [kp])
      have first := mul_le_mul_of_nonpos_left firstCap ln
      have last := mul_le_mul_of_nonpos_left lastCap (show -k≤0 by linarith only [kp])
      have strict := mul_pos (sub_pos.mpr side) (show 0<k-l by linarith only [kp,ln])
      have margin := transverse_before h.normal en h.sum ln
      dsimp [k,l,kappa,sigma] at formula first last strict margin sumIdentity
      nlinarith only [neighborV,mark,formula,first,last,strict,margin,sumIdentity]

/-- Reframe the actual successor, without changing either its side or
its point membership. The final missing point is a statement about E. -/
theorem negative_successor (C E : OpenSquare)
    (side : 1<C.side) (same : C.side=E.side) (h : C1092ElbowProfile.Profile C)
    (cM : C.Inside (-7/20) (-7/20))
    (M : E.Inside (7/20) (-7/20))
    (A : E.Inside (13/50) (-1)) (B : E.Inside (2/5) (-1))
    (G : ¬E.Inside 1 (-2/5)) (K : ¬E.Inside 1 (-1))
    (R : ¬E.Inside 0 (-543/500))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    ∃ F : OpenSquare,F.side=E.side ∧ (∀ x y,F.Inside x y↔E.Inside x y) ∧
      Normal F.c (-F.s) ∧ F.s<0 ∧ ¬E.Inside 0 (-13/50) := by
  obtain ⟨F,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame E
  have common : C.side=F.side := same.trans shape.symm
  have disjoint : ∀ x y,¬(C.Inside x y ∧ F.Inside x y) := fun x y both =>
    apart x y ⟨both.1,(inside _ _).mp both.2⟩
  have negative : F.s<0 := by
    apply lt_of_not_ge
    intro sign
    have normal : Normal F.c F.s := ⟨sign,
      by simpa only [abs_of_nonneg sign] using canonical,F.unit_normal⟩
    exact nonnegative_impossible C F side common h normal cM
      ((inside _ _).mpr M) ((inside _ _).mpr A) ((inside _ _).mpr B)
      (fun own => G ((inside _ _).mp own)) (fun own => K ((inside _ _).mp own))
      (fun own => R ((inside _ _).mp own)) disjoint
  have normal : Normal F.c (-F.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,
    by nlinarith only [F.unit_normal]⟩
  have missing : ¬E.Inside 0 (-13/50) := by
    intro own
    have T := (inside _ _).mpr own
    have A' := (inside _ _).mpr A
    have B' := (inside _ _).mpr B
    have X : F.Inside 0 (-1/2) := by
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [T.1,T.2.2.2,A'.2.2.1,B'.2.1,cp,negative,normal.2.1]
    exact disjoint 0 (-1/2) ⟨h.crosspoint,X⟩
  exact ⟨F,shape,inside,normal,negative,missing⟩

#print axioms nonnegative_impossible
#print axioms negative_successor
end N12Compact.C1092MPPMElbowSuccessor
