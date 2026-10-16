import Compact.Geometry.UpperRightCornerLongitudinal
import Compact.Geometry.UpperRightCornerTopTransverse
import Compact.Geometry.C977CornerHalfAngle

/-! The remaining top-owned longitudinal axis, and the resulting complete
positive/positive corner reach. All missing-point faces remain explicit. -/
namespace N12Compact.UpperRightCornerTopLongitudinal

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner UpperRightCornerLongitudinalBounds

private theorem corner_radial {c s : ℝ} (hn : Normal c s) : 1-c≤(3/5)*s^2 := by
  have b := normal_bounds hn
  have p := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(3/5)*(1+c)-1 by linarith only [b.1])
  nlinarith only [p,hn.2.2]

private theorem parallel_lower_margin {c s : ℝ} (hn : Normal c s) :
    0≤c+2*s-1-(9/5)*c*s := by
  have disk := disk_margin hn (a := 9/10) (b := 3/10) (by norm_num)
  have p := mul_nonneg hn.1 (show 0≤2-(9/5)*c-(3/5)*s by linarith only [disk])
  nlinarith only [p,corner_radial hn]

private theorem positive_lower_margin {c s d t : ℝ} (hn : Normal c s) (ht : Normal d t)
    (sign : 0≤c*t-s*d) :
    0≤s+(c*d+s*t)*(c+s-1)-(9/5)*d*s := by
  have cb := normal_bounds hn
  have db := normal_bounds ht
  have angles := ordered_normals hn ht sign
  have coefficient : c*(c+s-1)-(9/5)*s≤0 := by
    have p := mul_nonneg (sub_nonneg.mpr cb.2.1)
      (sub_nonneg.mpr cb.2.2.2.2.1)
    nlinarith only [p,cb.2.1,hn.1]
  have one := mul_nonneg (neg_nonneg.mpr coefficient) (sub_nonneg.mpr angles.1)
  have two := mul_nonneg (mul_nonneg hn.1 (sub_nonneg.mpr cb.2.2.2.2.1))
    (sub_nonneg.mpr angles.2)
  have identity : s+(c*d+s*t)*(c+s-1)-(9/5)*d*s =
      (c+2*s-1-(9/5)*c*s) -
      (c*(c+s-1)-(9/5)*s)*(c-d)+s*(c+s-1)*(t-s) := by
    linear_combination (c+s-1)*hn.2.2
  nlinarith only [one,two,parallel_lower_margin hn,identity]

private theorem negative_lower_margin {c s d t : ℝ} (hn : Normal c s) (ht : Normal d t)
    (sign : c*t-s*d≤0) :
    0≤s+s*(c*d+s*t)+d-(c*d+s*t)-(9/5)*d*s := by
  have cb := normal_bounds hn
  have db := normal_bounds ht
  let K := c*d+s*t
  have ku : K≤1 := dot_le_one hn ht
  by_cases shallow : s≤5/9
  · let a := c-1+s*(9/5-c)
    let b := s*(1-s)
    have ap : 0≤a := by
      have p := mul_nonneg hn.1
        (show 0≤9/5-c-(3/5)*s by linarith only [cb.2.1,cb.2.2.2.1])
      dsimp [a]
      nlinarith only [p,corner_radial hn]
    have slope : a*s≤b*c := by
      have p := mul_nonneg hn.1 (sub_nonneg.mpr shallow)
      dsimp [a,b]
      nlinarith only [p]
    have order : t≤s := sine_order hn ht sign
    have bound := linear_arc_max hn ht order ap slope
    have endpoint : a*c+b*s=s-(c+2*s-1-(9/5)*c*s) := by
      dsimp [a,b]
      linear_combination (1-s)*hn.2.2
    rw [endpoint] at bound
    dsimp [a,b] at bound
    nlinarith only [bound,parallel_lower_margin hn]
  · have one := mul_nonneg (sub_nonneg.mpr ku)
      (show 0≤1-s by linarith only [cb.2.2.2.1])
    have two := mul_nonneg (sub_nonneg.mpr db.2.1)
      (show 0≤(9/5)*s-1 by linarith only [shallow])
    dsimp [K] at one
    nlinarith only [one,two,hn.1]

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
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [low,above,row.2.1,row.2.2.1,cp,tn.1]
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
    clear_value K H
    nlinarith only [square,dotUnit,kp,sq_nonneg (K-7/10)]
  have faces : E.loU+E.side≤(7/2)*E.c+3*E.s ∨
      3*E.c-(7/2)*E.s≤E.loV := by
    by_cases high : E.loU+E.side≤(7/2)*E.c+3*E.s
    · exact Or.inl high
    · right
      apply le_of_not_gt
      intro low
      apply missingReach
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [high,low,outward.1,corner.2.2.2,ep,en.1]
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
      clear_value K H
      nlinarith only [base,separator,first,second,margin,size,identity]
    · have wall := UpperRightCornerLongitudinal.top_wall E box
      have a := mul_nonneg en.1 (sub_nonneg.mpr separator)
      have b := mul_nonneg en.1 (sub_nonneg.mpr base)
      have c := mul_nonneg kp.le (sub_nonneg.mpr wall)
      have d := mul_nonneg cp.le (sub_nonneg.mpr low)
      have margin := positive_lower_margin en tn sign
      change 0≤E.s+K*(E.c+E.s-1)-(9/5)*T.c*E.s at margin
      have positive : 0<E.s+K*(E.c+E.s) := by
        have product := mul_pos kp (show 0<E.c+E.s by linarith only [ep,en.1])
        linarith only [product,en.1]
      have size := mul_pos positive (sub_pos.mpr side)
      have identity :
          K*(4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side))+
            T.c*(E.loV-(3*E.c-(7/2)*E.s))+
            E.s*(K*E.loU+H*E.loV-((17/10)*T.c+3*T.s+E.side))=
          K+(9/5)*T.c*E.s-E.side*(E.s+K*(E.c+E.s)) := by
        dsimp [K,H]
        linear_combination (-T.c*E.loV)*en.2.2
      clear_value K H
      nlinarith only [a,b,c,d,identity,size,margin]
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
      clear_value K H
      nlinarith only [base,separator,first,second,margin,size,identity]
    · have wall := UpperRightCornerLongitudinal.top_wall E box
      have a := mul_nonneg en.1 (sub_nonneg.mpr separator)
      have b := mul_nonneg en.1 (sub_nonneg.mpr base)
      have c := mul_nonneg kp.le (sub_nonneg.mpr wall)
      have d := mul_nonneg cp.le (sub_nonneg.mpr low)
      have margin := negative_lower_margin en tn negative
      change 0≤E.s+E.s*K+T.c-K-(9/5)*T.c*E.s at margin
      have positive : 0<E.s+E.s*K+T.c := by
        have product := mul_nonneg en.1 kp.le
        linarith only [en.1,product,cp]
      have size := mul_pos positive (sub_pos.mpr side)
      have identity :
          K*(4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side))+
            T.c*(E.loV-(3*E.c-(7/2)*E.s))+
            E.s*(K*E.loU+H*(E.loV+E.side)-
              ((17/10)*T.c+3*T.s+E.side))=
          K+(9/5)*T.c*E.s-E.side*(E.s+E.s*K+T.c) := by
        dsimp [K,H]
        linear_combination (-T.c*(E.loV+E.side))*en.2.2
      clear_value K H
      nlinarith only [a,b,c,d,identity,size,margin]

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
