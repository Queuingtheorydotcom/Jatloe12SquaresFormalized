import Compact.Geometry.UpperRightCornerLongitudinalBounds
import Compact.Geometry.UpperRightCornerReachAxes
import Compact.Geometry.CentralWallEscape
import Compact.Geometry.C977NegativeCorner

/-! The E-owned longitudinal selector is excluded using the complete
top-wall support and the actual top container wall of E. Both missing-point
escapes, and both relative-angle signs, remain in the proof. -/
namespace N12Compact.UpperRightCornerLongitudinal

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner UpperRightCornerLongitudinalBounds

/-- The actual top wall carries a strict support surplus in every positive
canonical direction. This retains its full side, its two foreign-point
exclusions, and all of their lower-face alternatives. -/
theorem support_growth (T : OpenSquare) {e f : ℝ}
    (en : Normal e f) (tn : Normal T.c T.s) (side : 1<T.side)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20)) :
    (7/2)*e+3*f+(3/5)*f<upper T e f+T.side := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<e := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  let K := e*T.c+f*T.s
  let H := f*T.c-e*T.s
  have kp : 0<K := by
    have first := mul_pos ep cp
    have last := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [first,last]
  have wings : (87/50)*T.c+3*T.s≤T.loU ∨
      T.loV+T.side≤3*T.c-(87/50)*T.s := by
    by_cases low : (87/50)*T.c+3*T.s≤T.loU
    · exact Or.inl low
    · right
      apply le_of_not_gt
      intro high
      apply missingWing
      refine ⟨lt_of_not_ge low,?_,?_,?_⟩ <;>
        nlinarith only [row.2.1,row.2.2.1,high,cp,tn.1]
  have central : (47/20)*(T.c+T.s)≤T.loU ∨
      (47/20)*(T.c-T.s)≤T.loV := by
    by_cases low : (47/20)*(T.c+T.s)≤T.loU
    · exact Or.inl low
    · right
      apply le_of_not_gt
      intro below
      apply missingNE
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [low,below,row.2.1,marker.2.2.2,cp,tn.1]
  have short : (13/20)*T.c+(61/100)*T.s<1 := by
    have h := disk_margin tn (show (13/20 : ℝ)^2+(61/100)^2<1 by norm_num)
    linarith only [h]
  have incompatible
      (high : T.loV+T.side≤3*T.c-(87/50)*T.s)
      (low : (47/20)*(T.c-T.s)≤T.loV) : False := by
    linarith only [high,low,side,short]
  have positive_form (sign : 0≤H) :
      upper T e f=K*(T.loU+T.side)+H*(T.loV+T.side) := by
    rw [upper_in_bands]
    have second : -e*T.s+f*T.c=H := by dsimp [H]; ring
    rw [show e*T.c+f*T.s=K from rfl,second,
      abs_of_nonneg kp.le,abs_of_nonneg sign]
    ring
  have negative_form (sign : H≤0) :
      upper T e f=K*(T.loU+T.side)+H*T.loV := by
    rw [upper_in_bands]
    have second : -e*T.s+f*T.c=H := by dsimp [H]; ring
    rw [show e*T.c+f*T.s=K from rfl,second,
      abs_of_nonneg kp.le,abs_of_nonpos sign]
    ring
  by_cases sign : 0≤H
  · rw [positive_form sign]
    rcases central with lowU | lowV
    · have first := mul_nonneg kp.le (sub_nonneg.mpr lowU)
      have last := mul_nonneg sign
        (sub_nonneg.mpr (show 3*T.c-(12/5)*T.s≤T.loV+T.side by
          linarith only [row.2.2.2]))
      have width : 0<T.side-(13/20)*(T.c+T.s) := by
        linarith only [side,tb.2.2.2.2.2]
      have surplus := mul_pos kp width
      have positive := mul_nonneg sign (mul_nonneg
        (show (0 : ℝ)≤3/5 by norm_num) tn.1)
      have disk := disk_margin en (show (1/2 : ℝ)^2+(3/5)^2<1 by norm_num)
      have identity :
          K*((47/20)*(T.c+T.s)+T.side)+H*(3*T.c-(12/5)*T.s)=
          3*(e+f)+K*(T.side-(13/20)*(T.c+T.s))+(3/5)*T.s*H := by
        dsimp [K,H]
        linear_combination 3*(e+f)*tn.2.2
      nlinarith only [first,last,width,surplus,positive,disk,identity,side]
    · have lowU : (87/50)*T.c+3*T.s≤T.loU := by
        rcases wings with lowU | highV
        · exact lowU
        · exact False.elim (incompatible highV lowV)
      have first := mul_nonneg kp.le (sub_nonneg.mpr lowU)
      have last := mul_nonneg sign (sub_nonneg.mpr lowV)
      have size := mul_pos (show 0<K+H+1 by linarith only [kp,sign])
        (sub_pos.mpr side)
      have margin := lower_pair_margin en tn sign
      have identity :
          K*((87/50)*T.c+3*T.s)+H*((47/20)*(T.c-T.s))+K+H+1-
            ((7/2)*e+3*f+(3/5)*f)=
          1+e*(T.c-T.s-44/25+(61/100)*T.s^2+(13/20)*T.c*T.s)+
            f*(T.c+T.s-5/4+(13/20)*T.s^2-(61/100)*T.c*T.s) := by
        dsimp [K,H]
        linear_combination ((87/50)*e+(47/20)*f)*tn.2.2
      nlinarith only [first,last,size,margin,identity]
  · have negative : H≤0 := (lt_of_not_ge sign).le
    rw [negative_form negative]
    rcases wings with lowU | highV
    · have first := mul_nonneg kp.le (sub_nonneg.mpr lowU)
      have last := mul_nonneg (neg_nonneg.mpr negative)
        (sub_nonneg.mpr (show T.loV≤(1543/500)*T.c-2*T.s by
          linarith only [marker.2.2.1]))
      have size := mul_pos (show 0<K+1 by linarith only [kp]) (sub_pos.mpr side)
      have margin := marker_margin en tn
      have identity :
          K*((87/50)*T.c+3*T.s)+H*((1543/500)*T.c-2*T.s)+K+1-
            ((7/2)*e+3*f+(3/5)*f)=
          1+e*(T.c-44/25+(13/50)*T.s^2-(43/500)*T.c*T.s)+
            f*((43/500)*T.c^2+T.s-(13/50)*T.c*T.s-3/5) := by
        dsimp [K,H]
        linear_combination ((87/50)*e+3*f)*tn.2.2
      nlinarith only [first,last,size,margin,identity]
    · have lowU : (47/20)*(T.c+T.s)≤T.loU := by
        rcases central with lowU | lowV
        · exact lowU
        · exact False.elim (incompatible highV lowV)
      have tilt : (3/10)*T.c≤T.s := by
        nlinarith only [marker.2.2.2,highV,cp]
      have first := mul_nonneg kp.le (sub_nonneg.mpr lowU)
      have last := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr highV)
      have size := mul_pos (show 0<K-H+1 by linarith only [kp,negative])
        (sub_pos.mpr side)
      have margin := upper_pair_margin en tn negative tilt
      have identity :
          K*((47/20)*(T.c+T.s))+H*(3*T.c-(87/50)*T.s)+K-H+1-
            ((7/2)*e+3*f+(3/5)*f)=
          1+e*(T.c+T.s-23/20-(61/100)*T.s^2-(13/20)*T.c*T.s)+
            f*(T.s-T.c+(61/100)*T.c*T.s-(13/20)*T.s^2-3/5) := by
        dsimp [K,H]
        linear_combination ((47/20)*e+3*f)*tn.2.2
      nlinarith only [first,last,size,margin,identity]

theorem top_wall (E : OpenSquare) (box : InsideContainer E) :
    E.s*(E.loU+E.side)+E.c*(E.loV+E.side)≤4 := by
  have bound : 0≤4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side) := by
    apply affine_endpoint_nonnegative E.side (E.c+E.s) _ E.side_pos
    intro epsilon positive small
    let u := E.loU+E.side-epsilon
    let v := E.loV+E.side-epsilon
    have point : E.Inside (E.c*u-E.s*v) (E.s*u+E.c*v) := by
      apply (inside_iff_rotated_box E _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      exact ⟨by linarith only [small],by linarith only [positive],
        by linarith only [small],by linarith only [positive]⟩
    have high := (box _ _ point).2.2.2
    dsimp [u,v] at high
    nlinarith only [high]
  linarith only [bound]

/-- A complete longitudinal selector is excluded in both missing-reach
faces. The actual top wall of E is essential in the lower-V alternative. -/
theorem corner_axis_impossible (E T : OpenSquare)
    (en : Normal E.c E.s) (tn : Normal T.c T.s)
    (same : E.side=T.side) (side : 1<E.side) (box : InsideContainer E)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingReach : ¬E.Inside (7/2) 3)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : upper T E.c E.s≤E.loU) : False := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have growth := support_growth T en tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  rw [←same] at growth
  have faces : E.loU+E.side≤(7/2)*E.c+3*E.s ∨
      3*E.c-(7/2)*E.s≤E.loV := by
    by_cases high : E.loU+E.side≤(7/2)*E.c+3*E.s
    · exact Or.inl high
    · right
      apply le_of_not_gt
      intro low
      apply missingReach
      refine ⟨?_,lt_of_not_ge high,low,?_⟩ <;>
        nlinarith only [outward.1,corner.2.2.2,ep,en.1]
  rcases faces with high | low
  · nlinarith only [growth,separator,high,en.1]
  · have wall := top_wall E box
    have first := mul_nonneg en.1 (sub_nonneg.mpr separator)
    have second := mul_nonneg ep.le (sub_nonneg.mpr low)
    have third := mul_nonneg en.1 (sub_nonneg.mpr growth.le)
    have size := mul_pos ep (sub_pos.mpr side)
    have product := mul_nonneg (sub_nonneg.mpr eb.2.1)
      (show 0≤(3/5)*E.c-2/5 by linarith only [eb.1])
    have margin : 1≤E.c+(3/5)*E.s^2 := by
      nlinarith only [product,en.2.2]
    nlinarith only [wall,first,second,third,size,margin,en.2.2]

#print axioms support_growth
#print axioms corner_axis_impossible
end N12Compact.UpperRightCornerLongitudinal
