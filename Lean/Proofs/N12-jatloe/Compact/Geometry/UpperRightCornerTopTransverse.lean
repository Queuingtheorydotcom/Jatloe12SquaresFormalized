import Compact.Geometry.UpperRightCornerReachAxes
import Compact.Geometry.C977NegativeCorner

/-! The top square's transverse axis cannot separate it from a positive
northeast corner which misses the farther outer point. The genuine
foreign right-wall point supplies the lower face. All relative angles
are included; two endpoint inequalities replace angle subdivision. -/
namespace N12Compact.UpperRightCornerTopTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem small_sine {e f : ℝ} (normal : Normal e f) : f≤5/7 := by
  have bounds := normal_bounds normal
  linarith only [normal.2.1,bounds.2.2.2.2.2]

private theorem parallel_margin {e f : ℝ} (normal : Normal e f) :
    0<1-(3/5)*(e+f) := by
  have bounds := normal_bounds normal
  linarith only [bounds.2.2.2.2.2]

private theorem shallow_margin {e f c s : ℝ}
    (en : Normal e f) (tn : Normal c s) (order : e*s-f*c≤0) :
    0≤c*(e-(3/5)*e^2)+s*(f-3/5-(3/5)*e*f) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<e := by linarith only [eb.1]
  have cp : 0<c := by linarith only [tb.1]
  let A := e-(3/5)*e^2
  let B := f-3/5-(3/5)*e*f
  have radial := mul_nonneg en.1 (sub_nonneg.mpr eb.1)
  have bp : B≤0 := by
    have fs := small_sine en
    dsimp [B]
    nlinarith only [radial,fs]
  have endpoint : e*A+f*B=1-(3/5)*(e+f) := by
    dsimp [A,B]
    linear_combination (1-(3/5)*e)*en.2.2
  have first := mul_pos cp (parallel_margin en)
  have last := mul_nonneg (neg_nonneg.mpr order) (neg_nonneg.mpr bp)
  have identity : e*(c*A+s*B)=c*(e*A+f*B)+(e*s-f*c)*B := by ring
  have positive : 0<e*(c*A+s*B) := by
    rw [endpoint] at identity
    clear_value A B
    nlinarith only [identity,first,last]
  have result := pos_of_mul_pos_right positive ep.le
  change 0≤c*A+s*B
  exact result.le

private theorem steep_lower_margin {e f c s : ℝ}
    (en : Normal e f) (tn : Normal c s) (order : 0≤e*s-f*c) :
    0≤(e*c+f*s)*(1-f/2)-(3/5)*s := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<e := by linarith only [eb.1]
  have cp : 0≤c := by linarith only [tb.1]
  have first := mul_nonneg cp (sub_nonneg.mpr eb.2.1)
  have last := mul_nonneg en.1 order
  have identity : e*(e*c+f*s-c)=c*(1-e)+f*(e*s-f*c) := by
    linear_combination c*en.2.2
  have scaled : 0≤e*(e*c+f*s-c) := by
    linarith only [identity,first,last]
  have dot := nonneg_of_mul_nonneg_right scaled ep
  have fs := small_sine en
  have weighted := mul_nonneg dot (show 0≤1-f/2 by linarith only [fs])
  have slope := mul_nonneg (show 0≤(3/5 : ℝ) by norm_num)
    (sub_nonneg.mpr tn.2.1)
  have remainder := mul_nonneg cp (show 0≤2/5-f/2 by linarith only [fs])
  nlinarith only [weighted,slope,remainder]

private theorem steep_upper_margin {e f c s : ℝ}
    (en : Normal e f) (tn : Normal c s) (order : 0≤e*s-f*c) :
    0≤c*(e-f-(3/5)*e^2+e*f/2)+
      s*(e+f-11/10+f^2/2-(3/5)*e*f) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<e := by linarith only [eb.1]
  have cp : 0<c := by linarith only [tb.1]
  let A := e-f-(3/5)*e^2+e*f/2
  let B := e+f-11/10+f^2/2-(3/5)*e*f
  have parallel : e*A+f*B=1-(3/5)*(e+f) := by
    dsimp [A,B]
    linear_combination (1-(3/5)*e+f/2)*en.2.2
  have disk : e*f≤1/2 := by nlinarith only [en.2.2,sq_nonneg (e-f)]
  have radial := mul_nonneg (sub_nonneg.mpr eb.1) (sub_nonneg.mpr eb.2.1)
  have diagonal : 0<A+B := by
    dsimp [A,B]
    nlinarith only [radial,disk,en.2.2,eb.1]
  by_cases sign : 0≤B
  · have first := mul_pos cp (parallel_margin en)
    have last := mul_nonneg order sign
    have identity : e*(c*A+s*B)=c*(e*A+f*B)+(e*s-f*c)*B := by ring
    have positive : 0<e*(c*A+s*B) := by
      rw [parallel] at identity
      clear_value A B
      linarith only [identity,first,last]
    have result := pos_of_mul_pos_right positive ep.le
    exact result.le
  · have first := mul_pos cp diagonal
    have last := mul_nonneg (sub_nonneg.mpr tn.2.1)
      (show 0≤-B by linarith only [sign])
    change 0≤c*A+s*B
    nlinarith only [first,last]

/-- The reversed T-transverse alternative is excluded using actual
corner points and the missing right-wall point. The top square contributes
its strict row point; no translation or wall bound for T is assumed. -/
theorem impossible (E T : OpenSquare)
    (en : Normal E.c E.s) (tn : Normal T.c T.s) (side : 1<E.side)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (missingReach : ¬E.Inside (7/2) 3)
    (topRow : T.Inside (12/5) 3)
    (separator : upper E (-T.s) T.c≤T.loV) : False := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  have floor := UpperRightCornerReachAxes.lower_face E ep en.1 en.2.1 side
    corner outward missingRight missingReach
  let K := E.c*T.c+E.s*T.s
  let H := E.c*T.s-E.s*T.c
  have kp : 0<K := by
    have first := mul_pos ep cp
    have last := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [first,last]
  have top : T.loV<3*T.c-(12/5)*T.s := by linarith only [topRow.2.2.1]
  have faces : E.loU+E.side≤(7/2)*E.c+3*E.s ∨
      3*E.c-(7/2)*E.s≤E.loV := by
    by_cases cap : E.loU+E.side≤(7/2)*E.c+3*E.s
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro low
      apply missingReach
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [cap,low,outward.1,corner.2.2.2,ep,en.1]
  by_cases order : H≤0
  · have form : upper E (-T.s) T.c=
        -H*(E.loU+E.side)+K*(E.loV+E.side) := by
      rw [upper_in_bands]
      have first : (-T.s)*E.c+T.c*E.s=-H := by dsimp [H]; ring
      have second : -(-T.s)*E.s+T.c*E.c=K := by dsimp [K]; ring
      rw [first,second,abs_of_nonneg (neg_nonneg.mpr order),abs_of_nonneg kp.le]
      ring
    have first := mul_nonneg (neg_nonneg.mpr order)
      (sub_nonneg.mpr corner.2.1.le)
    have last := mul_nonneg kp.le (sub_nonneg.mpr floor)
    have excess := mul_pos kp (sub_pos.mpr side)
    have margin := shallow_margin en tn (show E.c*T.s-E.s*T.c≤0 from order)
    have identity :
        -H*(3*E.c+3*E.s)+K*((12/5)*E.c-3*E.s+1)-
          (3*T.c-(12/5)*T.s)=
        T.c*(E.c-(3/5)*E.c^2)+T.s*(E.s-3/5-(3/5)*E.c*E.s) := by
      dsimp [K,H]
      linear_combination 3*(T.c-T.s)*en.2.2
    clear_value K H
    nlinarith only [form,first,last,excess,margin,identity,separator,top]
  · have hp : 0≤H := (lt_of_not_ge order).le
    have form : upper E (-T.s) T.c=-H*E.loU+K*(E.loV+E.side) := by
      rw [upper_in_bands]
      have first : (-T.s)*E.c+T.c*E.s=-H := by dsimp [H]; ring
      have second : -(-T.s)*E.s+T.c*E.c=K := by dsimp [K]; ring
      rw [first,second,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg kp.le]
      ring
    rcases faces with cap | low
    · have first := mul_nonneg hp (sub_nonneg.mpr cap)
      have last := mul_nonneg kp.le (sub_nonneg.mpr floor)
      have excess := mul_pos (show 0<K+H by linarith only [kp,hp])
        (sub_pos.mpr side)
      have margin := steep_upper_margin en tn hp
      have identity :
          -H*((7/2)*E.c+3*E.s)+K*((12/5)*E.c-3*E.s)+(K+H)-
            (3*T.c-(12/5)*T.s)=
          T.c*(E.c-E.s-(3/5)*E.c^2+E.c*E.s/2)+
            T.s*(E.c+E.s-11/10+E.s^2/2-(3/5)*E.c*E.s) := by
        dsimp [K,H]
        linear_combination (3*T.c-(7/2)*T.s)*en.2.2
      clear_value K H
      nlinarith only [form,first,last,excess,margin,identity,separator,top]
    · have first := mul_nonneg hp (sub_nonneg.mpr corner.1.le)
      have last := mul_nonneg kp.le (sub_nonneg.mpr low)
      have excess := mul_pos kp (sub_pos.mpr side)
      have margin := steep_lower_margin en tn hp
      have identity :
          -H*(3*E.c+3*E.s)+K*(3*E.c-(7/2)*E.s+1)-
            (3*T.c-(12/5)*T.s)=K*(1-E.s/2)-(3/5)*T.s := by
        dsimp [K,H]
        linear_combination 3*(T.c-T.s)*en.2.2
      change 0≤K*(1-E.s/2)-(3/5)*T.s at margin
      clear_value K H
      nlinarith only [form,first,last,excess,margin,identity,separator,top]

#print axioms impossible
end N12Compact.UpperRightCornerTopTransverse
