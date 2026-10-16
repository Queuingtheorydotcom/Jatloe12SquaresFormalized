import Compact.Geometry.C849SteepAB
import Compact.Geometry.C849ShallowMargins

/-! The complementary shallow positive-B sector. Both remaining separating
axes come from actual disjointness; A retains its full compulsory triangle.
The relative-angle split is continuous, with no sampled angles. -/
namespace N12Compact.C849ShallowAB

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C849SteepAB

theorem in_frame (A B : OpenSquare)
    (ap : 0 < A.c) (aq : 0 ≤ A.s) (bc : 0 < B.c) (bs : 0 ≤ B.s)
    (lowSlope : 3*B.c ≤ 7*B.s) (highSlope : B.s ≤ (4/5)*B.c)
    (same : A.side = B.side) (ha : 1 < B.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (missingR : ¬ A.Inside 3 (12/5))
    (bT : ClosedInside B (33/20) (47/20)) (bH : B.Inside 2 (1543/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) : False := by
  have bpos : 0 < B.s := by linarith only [bc,lowSlope]
  have bsc : B.s ≤ B.c := by linarith only [bc,highSlope]
  have aTclosed : ClosedInside A (47/20) (47/20) :=
    ⟨aT.1.le,aT.2.1.le,aT.2.2.1.le,aT.2.2.2.le⟩
  have axes := ABTransverse.alternatives A B ap aq bc bpos same aP aQ aTclosed bT bH apart
  have modes := face_modes A ap aq (by simpa only [same] using ha)
    aP aQ aT missingG missingB missingR
  let d := B.c*A.c+B.s*A.s
  let e := B.c*A.s-B.s*A.c
  have dPos : 0 < d := add_pos_of_pos_of_nonneg (mul_pos bc ap) (mul_nonneg bs aq)
  have dNonneg := dPos.le
  have fromA : e*(A.c*(33/20)+A.s*(47/20))+
      d*(-A.s*(33/20)+A.c*(47/20)) = -B.s*(33/20)+B.c*(47/20) :=
    compose A B (33/20) (47/20)
  have fromB : -e*(B.c*(33/20)+B.s*(47/20))+
      d*(-B.s*(33/20)+B.c*(47/20)) = -A.s*(33/20)+A.c*(47/20) := by
    have identity := compose B A (33/20) (47/20)
    dsimp [e,d]
    nlinarith only [identity]
  have maxFormula := upper_formula A B dNonneg
  have minFormula := lower_formula A B dNonneg
  change upper A (-B.s) B.c = e*(A.loU+A.side/2)+d*(A.loV+A.side/2)+
    A.side/2*(|e|+d) at maxFormula
  change lower B (-A.s) A.c = -e*(B.loU+B.side/2)+d*(B.loV+B.side/2)-
    B.side/2*(|e|+d) at minFormula
  rw [same] at maxFormula axes
  have order_of_cross (cross : e ≤ 0) : A.s ≤ A.c := by
    have product := mul_nonneg ap.le (sub_nonneg.mpr bsc)
    by_contra failure
    have positive := mul_pos bc (sub_pos.mpr (lt_of_not_ge failure))
    dsimp [e] at cross
    nlinarith only [cross,product,positive]
  have span : (7/10)*(A.c+A.s) ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s),sq_nonneg (A.c+A.s-10/7)]
  have wide : 0 < (B.side-1)*d := mul_pos (sub_pos.mpr ha) dPos
  have bPoint := (ABTransverse.closed_bounds B (33/20) (47/20)
    (-A.s) A.c bT).1
  rcases modes with ⟨uBound,vBound,order⟩ | ⟨uBound,vBound,qBound⟩
  · rcases axes with axisB | axisA
    · by_cases cross : 0 ≤ e
      · rw [maxFormula,abs_of_nonneg cross] at axisB
        have hU := mul_nonneg cross (sub_nonneg.mpr uBound)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have spanProduct := mul_nonneg dNonneg (sub_nonneg.mpr span)
        have extra := mul_nonneg cross (show 0 ≤ B.side by linarith only [ha])
        clear_value d e
        nlinarith only [axisB,bT.2.2.1,hU,hV,spanProduct,extra,wide,fromA]
      · have negative : e ≤ 0 := le_of_not_ge cross
        rw [maxFormula,abs_of_nonpos negative] at axisB
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr aP.1)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have margin := C849ShallowMargins.lowerV_b_neg A.c A.s B.c B.s
          ap aq A.unit_normal bc bs highSlope negative
        change 0 < d*(1-(7/10)*(A.c+A.s))+e*((7/20)*A.c-(9/100)*A.s) at margin
        clear_value d e
        nlinarith only [axisB,bT.2.2.1,hU,hV,wide,fromA,margin]
    · nlinarith only [axisA,bPoint,vBound,span,ha]
  · rcases axes with axisB | axisA
    · by_cases cross : 0 ≤ e
      · rw [maxFormula,abs_of_nonneg cross] at axisB
        have hU := mul_nonneg cross (sub_nonneg.mpr uBound)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have width := mul_pos (sub_pos.mpr ha) (show 0 < d+e by linarith only [dPos,cross])
        have margin := C849ShallowMargins.lowerU_b_pos A.c A.s B.c B.s
          ap.le qBound A.unit_normal bc highSlope
        change 0 < d+e+(7/10)*e*(A.c-A.s)+d*((1/20)*A.c-(27/20)*A.s) at margin
        clear_value d e
        nlinarith only [axisB,bT.2.2.1,hU,hV,width,fromA,margin]
      · have negative : e ≤ 0 := le_of_not_ge cross
        have order := order_of_cross negative
        rw [maxFormula,abs_of_nonpos negative] at axisB
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr aP.1)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have margin := C849ShallowMargins.lowerV_b_neg A.c A.s B.c B.s
          ap aq A.unit_normal bc bs highSlope negative
        change 0 < d*(1-(7/10)*(A.c+A.s))+e*((7/20)*A.c-(9/100)*A.s) at margin
        have correction := mul_nonneg dNonneg
          (show 0 ≤ (3/4)*A.c-(13/20)*A.s by linarith only [order,ap])
        clear_value d e
        nlinarith only [axisB,bT.2.2.1,hU,hV,wide,fromA,margin,correction]
    · by_cases cross : 0 ≤ e
      · rw [minFormula,abs_of_nonneg cross] at axisA
        have hU := mul_nonneg cross (sub_nonneg.mpr bH.2.1.le)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr bT.2.2.1)
        have margin := C849ShallowMargins.lowerU_a_pos A.c A.s B.c B.s
          ap.le aq A.unit_normal bc bs B.unit_normal lowSlope highSlope
        change 0 < 1+(1/20)*A.c-(27/20)*A.s+e*((7/20)*B.c+(92/125)*B.s) at margin
        nlinarith only [axisA,hU,hV,vBound,ha,fromB,margin]
      · have negative : e ≤ 0 := le_of_not_ge cross
        have order := order_of_cross negative
        have square := mul_nonneg (sub_nonneg.mpr order) (add_nonneg ap.le aq)
        have qHigh : A.s ≤ 71/100 := by
          nlinarith only [A.unit_normal,square,aq,sq_nonneg (A.s-71/100)]
        nlinarith only [axisA,bPoint,vBound,ha,qHigh,ap]

#print axioms in_frame

end N12Compact.C849ShallowAB
