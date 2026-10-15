import Compact.Geometry.UpperRightCornerLongitudinal
import Compact.Geometry.UpperRightCornerTopTransverse

/-! The remaining top-owned longitudinal axis, and the resulting complete
positive/positive corner reach. All missing-point faces remain explicit. -/
namespace N12Compact.UpperRightCornerTopLongitudinal

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner UpperRightCornerLongitudinalBounds

/-- Both genuine foreign-point exclusions push the same full lower face.
The wing-upper-V escape must use the northeast marker's lower-U face. -/
theorem top_lower (T : OpenSquare) (tn : Normal T.c T.s) (side : 1<T.side)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20)) :
    (17/10)*T.c+3*T.s≤T.loU := by
  have bounds := normal_bounds tn
  have cp : 0<T.c := by linarith only [bounds.1]
  by_cases low : (87/50)*T.c+3*T.s≤T.loU
  · linarith only [low,cp]
  have high : T.loV+T.side≤3*T.c-(87/50)*T.s := by
    apply le_of_not_gt
    intro above
    apply missingWing
    refine ⟨lt_of_not_ge low,?_,?_,above⟩ <;>
      nlinarith only [row.2.1,row.2.2.1,cp,tn.1]
  have central : (47/20)*(T.c+T.s)≤T.loU := by
    apply le_of_not_gt
    intro below
    have lowerV : (47/20)*(T.c-T.s)≤T.loV := by
      apply le_of_not_gt
      intro lower
      apply missingNE
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [below,lower,row.2.1,marker.2.2.2,cp,tn.1]
    have short := disk_margin tn
      (show (13/20 : ℝ)^2+(61/100)^2<1 by norm_num)
    linarith only [high,lowerV,short,side]
  nlinarith only [central,tn.2.1]

/-- The T-owned U separator cannot coexist with either escape face of
the proposed corner reach. No side upper bound is used. -/
theorem impossible (E T : OpenSquare)
    (en : Normal E.c E.s) (tn : Normal T.c T.s)
    (same : E.side=T.side) (side : 1<E.side) (box : InsideContainer E)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingReach : ¬E.Inside (7/2) 3)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : T.loU+T.side≤lower E T.c T.s) : False := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  have base := top_lower T tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  rw [←same] at separator
  let K := E.c*T.c+E.s*T.s
  let H := E.c*T.s-E.s*T.c
  have kp : 0<K := by
    have first := mul_pos ep cp
    have second := mul_nonneg en.1 tn.1
    dsimp [K]; linarith only [first,second]
  have dotUnit : K^2+H^2=1 := by
    dsimp [K,H]
    linear_combination (T.c^2+T.s^2)*en.2.2+tn.2.2
  have plus : 0≤K+H := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr en.2.1)
    have second := mul_nonneg tn.1 (show 0≤E.c+E.s by linarith only [ep,en.1])
    dsimp [K,H]; nlinarith only [first,second]
  have minus : 0≤K-H := by
    have first := mul_nonneg ep.le (sub_nonneg.mpr tn.2.1)
    have second := mul_nonneg en.1 (show 0≤T.c+T.s by linarith only [cp,tn.1])
    dsimp [K,H]; nlinarith only [first,second]
  have kLower : 7/10≤K := by
    have square := mul_nonneg plus minus
    nlinarith only [square,dotUnit,kp,sq_nonneg (K-7/10)]
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
  have lowerPositive (sign : 0≤H) :
      lower E T.c T.s=K*E.loU+H*E.loV := by
    rw [lower_in_bands]
    have first : T.c*E.c+T.s*E.s=K := by dsimp [K]; ring
    have second : -T.c*E.s+T.s*E.c=H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonneg sign]
    ring
  have lowerNegative (sign : H≤0) :
      lower E T.c T.s=K*E.loU+H*(E.loV+E.side) := by
    rw [lower_in_bands]
    have first : T.c*E.c+T.s*E.s=K := by dsimp [K]; ring
    have second : -T.c*E.s+T.s*E.c=H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonpos sign]
    ring
  by_cases sign : 0≤H
  · rw [lowerPositive sign] at separator
    rcases faces with high | low
    · have first := mul_nonneg kp.le (sub_nonneg.mpr high)
      have second := mul_nonneg sign (sub_nonneg.mpr
        (show E.loV≤3*E.c-(16/5)*E.s by linarith only [outward.2.2.1]))
      have kc : T.c≤K := by
        have a := mul_nonneg en.1 sign
        have b := mul_nonneg cp.le (sub_nonneg.mpr eb.2.1)
        have identity : E.c*(K-T.c)=E.s*H+T.c*(1-E.c) := by
          dsimp [K,H]
          linear_combination T.c*en.2.2
        have scaled : 0≤E.c*(K-T.c) := by linarith only [identity,a,b]
        exact sub_nonneg.mp (nonneg_of_mul_nonneg_right scaled ep)
      have factor : 7/10≤1-(3/10)*E.c := by linarith only [eb.2.1]
      have m1 := mul_nonneg (sub_nonneg.mpr kc)
        (show 0≤1-(3/10)*E.c by linarith only [factor])
      have m2 := mul_nonneg cp.le (sub_nonneg.mpr factor)
      have margin : 0<1-(3/2)*T.c+K*(1-(3/10)*E.c) := by
        nlinarith only [m1,m2,tb.2.1]
      have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have identity :
          K*((7/2)*E.c+3*E.s)+H*(3*E.c-(16/5)*E.s)=
          (16/5)*T.c+3*T.s+(3/10)*E.c*K := by
        dsimp [K,H]
        linear_combination ((16/5)*T.c+3*T.s)*en.2.2
      nlinarith only [base,separator,first,second,margin,size,identity]
    · have wall := UpperRightCornerLongitudinal.top_wall E box
      have a := mul_nonneg en.1 (sub_nonneg.mpr separator)
      have b := mul_nonneg en.1 (sub_nonneg.mpr base)
      have c := mul_nonneg kp.le (sub_nonneg.mpr wall)
      have d := mul_nonneg cp.le (sub_nonneg.mpr low)
      have margin1 := mul_nonneg en.1
        (show 0≤1-(4/5)*T.c by linarith only [tb.2.1])
      have margin2 := mul_nonneg kp.le (sub_nonneg.mpr eb.2.2.2.2.1)
      have positive : 0<E.s+K*(E.c+E.s) := by
        have product := mul_pos kp (show 0<E.c+E.s by linarith only [ep,en.1])
        linarith only [product,en.1]
      have size := mul_pos positive (sub_pos.mpr side)
      have identity :
          K*(4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side))+
            T.c*(E.loV-(3*E.c-(7/2)*E.s))+
            E.s*(K*E.loU+H*E.loV-((17/10)*T.c+3*T.s+E.side))=
          K+(4/5)*T.c*E.s-E.side*(E.s+K*(E.c+E.s)) := by
        dsimp [K,H]
        linear_combination (-T.c*E.loV)*en.2.2
      nlinarith only [a,b,c,d,identity,size,margin1,margin2]
  · have negative : H≤0 := (lt_of_not_ge sign).le
    rw [lowerNegative negative] at separator
    rcases faces with high | low
    · have first := mul_nonneg kp.le (sub_nonneg.mpr high)
      have second := mul_nonneg (neg_nonneg.mpr negative)
        (sub_nonneg.mpr (show 3*E.c-3*E.s≤E.loV+E.side by
          linarith only [corner.2.2.2]))
      have factor : 1/2≤1-E.c/2 := by linarith only [eb.2.1]
      have m1 := mul_nonneg kp.le (sub_nonneg.mpr factor)
      have margin : 0<1-(13/10)*T.c+K*(1-E.c/2) := by
        nlinarith only [m1,kLower,tb.2.1]
      have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
      have identity :
          K*((7/2)*E.c+3*E.s)+H*(3*E.c-3*E.s)=
          3*T.c+3*T.s+(1/2)*E.c*K := by
        dsimp [K,H]
        linear_combination (3*T.c+3*T.s)*en.2.2
      nlinarith only [base,separator,first,second,margin,size,identity]
    · have wall := UpperRightCornerLongitudinal.top_wall E box
      have a := mul_nonneg en.1 (sub_nonneg.mpr separator)
      have b := mul_nonneg en.1 (sub_nonneg.mpr base)
      have c := mul_nonneg kp.le (sub_nonneg.mpr wall)
      have d := mul_nonneg cp.le (sub_nonneg.mpr low)
      have correction := mul_nonneg cp.le
        (show 0≤E.c-7/10 by linarith only [eb.1])
      have sine : T.s≤5/7 := by
        linarith only [tn.2.1,tb.2.2.2.2.2]
      have bracket : 0≤1-T.s+T.c*(E.c-4/5)+E.s*T.s := by
        have last := mul_nonneg en.1 tn.1
        nlinarith only [correction,last,tb.2.1,sine]
      have margin1 := mul_nonneg cp.le (sub_nonneg.mpr eb.2.1)
      have margin2 := mul_nonneg en.1 bracket
      have positive : 0<E.s+E.s*K+T.c := by
        have product := mul_nonneg en.1 kp.le
        linarith only [en.1,product,cp]
      have size := mul_pos positive (sub_pos.mpr side)
      have identity :
          K*(4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side))+
            T.c*(E.loV-(3*E.c-(7/2)*E.s))+
            E.s*(K*E.loU+H*(E.loV+E.side)-
              ((17/10)*T.c+3*T.s+E.side))=
          K+(4/5)*T.c*E.s-E.side*(E.s+E.s*K+T.c) := by
        dsimp [K,H]
        linear_combination (-T.c*(E.loV+E.side))*en.2.2
      have marginIdentity :
          E.s+E.s*K+T.c-K-(4/5)*T.c*E.s=
          T.c*(1-E.c)+E.s*(1-T.s+T.c*(E.c-4/5)+E.s*T.s) := by
        dsimp [K]; ring
      nlinarith only [a,b,c,d,identity,size,margin1,margin2,marginIdentity]

/-- The complete positive-corner/positive-top-wall statement, preserving
the actual foreign right-wall point as well as the full disjoint squares. -/
theorem point (E T : OpenSquare)
    (en : Normal E.c E.s) (tn : Normal T.c T.s)
    (same : E.side=T.side) (side : 1<E.side) (box : InsideContainer E)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)) :
    E.Inside (7/2) 3 := by
  by_contra missing
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have axes := UpperRightCornerReachAxes.alternatives E T
    (by linarith only [eb.1]) en.1 en.2.1
    (by linarith only [tb.1]) tn.1 tn.2.1 same side
    corner outward missingRight missing marker row apart
  rcases axes with eu | tu | tv
  · exact UpperRightCornerLongitudinal.corner_axis_impossible E T en tn
      same side box corner outward missing marker row missingWing missingNE eu
  · exact impossible E T en tn same side box corner outward missing
      marker row missingWing missingNE tu
  · exact UpperRightCornerTopTransverse.impossible E T en tn side
      corner outward missingRight missing row tv

#print axioms top_lower
#print axioms impossible
#print axioms point
end N12Compact.UpperRightCornerTopLongitudinal
