import Compact.Geometry.ABTransverse
import Compact.Geometry.C849SteepMargins
import Compact.Geometry.C849PositiveAbove
import Compact.Geometry.FourSquareAAll

/-! A complete geometric sector exclusion for the original 849/851 roles.
A's entire compulsory triangle and missing lower marker are essential.
This does not replace A by its forced point and does not assume a separating
axis. The two remaining transverse axes are derived from actual disjointness.
The final wrapper retains the original R square and its wall premises. -/
namespace N12Compact.C849SteepAB

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse

theorem compose (A B : OpenSquare) (x y : ℝ) :
    (B.c*A.s-B.s*A.c)*(A.c*x+A.s*y)+
      (B.c*A.c+B.s*A.s)*(-A.s*x+A.c*y) = -B.s*x+B.c*y := by
  calc
    _ = (A.c^2+A.s^2)*(-B.s*x+B.c*y) := by ring
    _ = _ := by rw [A.unit_normal,one_mul]

theorem upper_formula (A B : OpenSquare)
    (dot : 0≤B.c*A.c+B.s*A.s) :
    upper A (-B.s) B.c =
      (B.c*A.s-B.s*A.c)*(A.loU+A.side/2)+
      (B.c*A.c+B.s*A.s)*(A.loV+A.side/2)+
      A.side/2*(|B.c*A.s-B.s*A.c|+(B.c*A.c+B.s*A.s)) := by
  simp only [upper,supportRadius,
    show -B.s*A.c+B.c*A.s=B.c*A.s-B.s*A.c by ring,
    show -(-B.s)*A.s+B.c*A.c=B.c*A.c+B.s*A.s by ring,
    abs_of_nonneg dot]
  dsimp [centerX,centerY]
  ring

theorem lower_formula (A B : OpenSquare)
    (dot : 0≤B.c*A.c+B.s*A.s) :
    lower B (-A.s) A.c =
      -(B.c*A.s-B.s*A.c)*(B.loU+B.side/2)+
      (B.c*A.c+B.s*A.s)*(B.loV+B.side/2)-
      B.side/2*(|B.c*A.s-B.s*A.c|+(B.c*A.c+B.s*A.s)) := by
  simp only [lower,supportRadius,
    show -A.s*B.c+A.c*B.s=-(B.c*A.s-B.s*A.c) by ring,
    show -(-A.s)*B.s+A.c*B.c=B.c*A.c+B.s*A.s by ring,
    abs_neg,abs_of_nonneg dot]
  dsimp [centerX,centerY]
  ring

theorem face_modes (A : OpenSquare) (ap : 0<A.c) (aq : 0≤A.s)
    (ha : 1<A.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (missingR : ¬A.Inside 3 (12/5)) :
    ((A.c*(33/20)+A.s*(47/20)≤A.loU) ∧
      (-A.s*(47/20)+A.c*(33/20)≤A.loV) ∧ A.s≤A.c) ∨
    ((A.c*(47/20)+A.s*(33/20)≤A.loU) ∧
      (-A.s*3+A.c*(12/5)≤A.loV) ∧ 3/7≤A.s) := by
  have gUpperU : A.c*(47/20)+A.s*(33/20)<A.loU+A.side := by
    linarith only [aT.2.1,aq]
  have gUpperV : -A.s*(47/20)+A.c*(33/20)<A.loV+A.side := by
    linarith only [aP.2.2.2,ap,aq]
  have modes : A.c*(47/20)+A.s*(33/20)≤A.loU ∨
      -A.s*(47/20)+A.c*(33/20)≤A.loV := by
    by_cases below : A.c*(47/20)+A.s*(33/20)≤A.loU
    · exact Or.inl below
    · exact Or.inr (le_of_not_gt (fun lower =>
        missingG ⟨lt_of_not_ge below,gUpperU,lower,gUpperV⟩))
  have right_mode (lowerU : A.c*(47/20)+A.s*(33/20)≤A.loU) :
      (A.c*(47/20)+A.s*(33/20)≤A.loU) ∧
      (-A.s*3+A.c*(12/5)≤A.loV) ∧ 3/7≤A.s := by
    have angle : 35*A.c≤61*A.s := by linarith only [lowerU,aP.1]
    have short := (short_projections A (13/20) (3/4) (by norm_num)).2.1
    have rLowerU : A.loU<A.c*3+A.s*(12/5) := by linarith only [aT.1,ap,aq]
    have rUpperU : A.c*3+A.s*(12/5)<A.loU+A.side := by linarith only [lowerU,short,ha]
    have rUpperV : -A.s*3+A.c*(12/5)<A.loV+A.side := by
      linarith only [aP.2.2.2,angle,ap]
    have rLowerV : -A.s*3+A.c*(12/5)≤A.loV := le_of_not_gt
      (fun lower => missingR ⟨rLowerU,rUpperU,lower,rUpperV⟩)
    have square := mul_nonneg (sub_nonneg.mpr angle)
      (show 0≤61*A.s+35*A.c by linarith only [aq,ap])
    exact ⟨lowerU,rLowerV,by
      nlinarith only [square,A.unit_normal,aq,sq_nonneg (A.s-3/7)]⟩
  rcases modes with lowerU | lowerV
  · exact Or.inr (right_mode lowerU)
  ·
    have span : (7/10)*(A.c+A.s)≤1 := by
      nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s),sq_nonneg (A.c+A.s-10/7)]
    have bUpperU : A.c*(33/20)+A.s*(47/20)<A.loU+A.side := by
      linarith only [aT.2.1,ap]
    have bLowerV : A.loV < -A.s*(33/20)+A.c*(47/20) := by
      linarith only [aQ.2.2.1,ap,aq]
    have bUpperV : -A.s*(33/20)+A.c*(47/20)<A.loV+A.side := by
      linarith only [lowerV,span,ha]
    have bLowerU : A.c*(33/20)+A.s*(47/20)≤A.loU := le_of_not_gt
      (fun lower => missingB ⟨lower,bUpperU,bLowerV,bUpperV⟩)
    by_cases order : A.s≤A.c
    · exact Or.inl ⟨bLowerU,lowerV,order⟩
    · -- The steeper orientation belongs to the other face alternative.
      exact Or.inr (right_mode (by linarith only [bLowerU,lt_of_not_ge order]))

/-- Complete A/B contradiction in positive frames once the upper-left
marker uses B's upper transverse face. Every support bound below is
derived from the actual square faces and compulsory points. -/
theorem in_frame (A B : OpenSquare)
    (ap : 0<A.c) (aq : 0≤A.s) (bc : 0<B.c) (bs : 0≤B.s)
    (bsc : B.s≤B.c) (same : A.side=B.side) (ha : 1<B.side)
    (height : B.side≤B.s+B.c/2)
    (vCap : B.loV+B.side≤-B.s+3*B.c)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (missingR : ¬A.Inside 3 (12/5))
    (bT : ClosedInside B (33/20) (47/20)) (bH : B.Inside 2 (1543/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) : False := by
  have b := C849SteepMargins.bounds B.c B.s B.side bc bs bsc B.unit_normal ha height
  have bpos : 0<B.s := by linarith only [b.sLow]
  have haA : 1<A.side := by simpa only [same] using ha
  have aTclosed : ClosedInside A (47/20) (47/20) :=
    ⟨aT.1.le,aT.2.1.le,aT.2.2.1.le,aT.2.2.2.le⟩
  have axes := ABTransverse.alternatives A B ap aq bc bpos same aP aQ aTclosed bT bH apart
  have modes := face_modes A ap aq haA aP aQ aT missingG missingB missingR
  let d := B.c*A.c+B.s*A.s
  let e := B.c*A.s-B.s*A.c
  have dNonneg : 0≤d := add_nonneg (mul_nonneg bc.le ap.le) (mul_nonneg bs aq)
  have fromA : e*(A.c+3*A.s)+d*(-A.s+3*A.c)=-B.s+3*B.c := by
    dsimp [e,d]
    nlinarith only [compose A B 1 3]
  have fromB : -e*(B.c+3*B.s)+d*(-B.s+3*B.c)=-A.s+3*A.c := by
    have identity := compose B A 1 3
    dsimp [e,d]
    nlinarith only [identity]
  have maxFormula := upper_formula A B dNonneg
  have minFormula := lower_formula A B dNonneg
  change upper A (-B.s) B.c = e*(A.loU+A.side/2)+d*(A.loV+A.side/2)+
    A.side/2*(|e|+d) at maxFormula
  change lower B (-A.s) A.c = -e*(B.loU+B.side/2)+d*(B.loV+B.side/2)-
    B.side/2*(|e|+d) at minFormula
  rw [same] at maxFormula axes
  have bUpperU : 2*B.c+3*B.s≤B.loU+B.side := by
    linarith only [bH.2.1,bs]
  have bLowerU : B.loU≤B.c*(33/20)+B.s*(47/20) := bT.1
  have order_of_cross (cross : e≤0) : A.s≤A.c := by
    have product := mul_nonneg ap.le (sub_nonneg.mpr bsc)
    apply le_of_not_gt
    intro failure
    have positive := mul_pos bc (sub_pos.mpr failure)
    dsimp [e] at cross
    nlinarith only [cross,product,positive]
  have width : 0<(B.side-1)*(1+d) := mul_pos (sub_pos.mpr ha) (by linarith only [dNonneg])
  rcases modes with ⟨uBound,vBound,order⟩ | ⟨uBound,vBound,qBound⟩
  · rcases axes with axisB | axisA
    · by_cases cross : 0≤e
      · rw [maxFormula,abs_of_nonneg cross] at axisB
        have hU := mul_nonneg cross (sub_nonneg.mpr uBound)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have wide := mul_pos (sub_pos.mpr ha) (show 0<1+d+e by linarith only [dNonneg,cross])
        have margin := C849SteepMargins.lowerV_b_pos A.c A.s B.c B.s
          ap.le aq A.unit_normal B.unit_normal bc.le bs order cross
        change 0<1+d+e+(13/20)*e*(A.c-A.s)-(27/20)*d*(A.c+A.s) at margin
        clear_value d e
        nlinarith only [axisB,vCap,hU,hV,wide,fromA,margin]
      · have negative : e≤0 := le_of_not_ge cross
        rw [maxFormula,abs_of_nonpos negative] at axisB
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr aP.1)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have margin := C849SteepMargins.lowerV_b_neg A.c A.s B.c B.s
          ap.le aq A.unit_normal bc.le bs order bsc b.sumHigh
        change 0<1+d+e*(A.c-(37/50)*A.s)-(27/20)*d*(A.c+A.s) at margin
        clear_value d e
        nlinarith only [axisB,vCap,hU,hV,width,fromA,margin]
    · by_cases cross : 0≤e
      · rw [minFormula,abs_of_nonneg cross] at axisA
        have hU := mul_nonneg cross (sub_nonneg.mpr bUpperU)
        have hV := mul_nonneg dNonneg (show 0≤-B.s+3*B.c-B.side-B.loV by linarith only [vCap])
        have margin := C849SteepMargins.lowerV_a_pos A.c A.s B.c B.s
          ap.le aq A.unit_normal b cross
        change 0<1+d-(27/20)*(A.c+A.s)+e*B.c at margin
        clear_value d e
        nlinarith only [axisA,hU,hV,vBound,width,fromB,margin]
      · have negative : e≤0 := le_of_not_ge cross
        rw [minFormula,abs_of_nonpos negative] at axisA
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr bLowerU)
        have hV := mul_nonneg dNonneg (show 0≤-B.s+3*B.c-B.side-B.loV by linarith only [vCap])
        have margin := C849SteepMargins.lowerV_a_neg A.c A.s B.c B.s ap.le aq A.unit_normal b
        change 0<1+d-(27/20)*(A.c+A.s)+(13/20)*e*(B.c-B.s) at margin
        clear_value d e
        nlinarith only [axisA,hU,hV,vBound,width,fromB,margin]
  · rcases axes with axisB | axisA
    · by_cases cross : 0≤e
      · rw [maxFormula,abs_of_nonneg cross] at axisB
        have hU := mul_nonneg cross (sub_nonneg.mpr uBound)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have wide := mul_pos (sub_pos.mpr ha) (show 0<1+d+e by linarith only [dNonneg,cross])
        have margin := C849SteepMargins.lowerU_b_pos A.c A.s B.c B.s
          ap.le qBound A.unit_normal bc.le bs bsc b.sumHigh
        change 0<1+d+e+(27/20)*e*(A.c-A.s)-d*(2*A.s+(3/5)*A.c) at margin
        clear_value d e
        nlinarith only [axisB,vCap,hU,hV,wide,fromA,margin]
      · have negative : e≤0 := le_of_not_ge cross
        have order := order_of_cross negative
        rw [maxFormula,abs_of_nonpos negative] at axisB
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr aP.1)
        have hV := mul_nonneg dNonneg (sub_nonneg.mpr vBound)
        have margin := C849SteepMargins.lowerV_b_neg A.c A.s B.c B.s
          ap.le aq A.unit_normal bc.le bs order bsc b.sumHigh
        change 0<1+d+e*(A.c-(37/50)*A.s)-(27/20)*d*(A.c+A.s) at margin
        have correction := mul_nonneg dNonneg
          (show 0≤(3/4)*A.c-(13/20)*A.s by linarith only [order,ap])
        clear_value d e
        nlinarith only [axisB,vCap,hU,hV,width,fromA,margin,correction]
    · by_cases cross : 0≤e
      · rw [minFormula,abs_of_nonneg cross] at axisA
        have hU := mul_nonneg cross (sub_nonneg.mpr bUpperU)
        have hV := mul_nonneg dNonneg (show 0≤-B.s+3*B.c-B.side-B.loV by linarith only [vCap])
        have margin := C849SteepMargins.lowerU_a_pos A.c A.s B.c B.s
          ap.le aq A.unit_normal B.unit_normal b
        change 0<1+d-(2*A.s+(3/5)*A.c)+e*B.c at margin
        clear_value d e
        nlinarith only [axisA,hU,hV,vBound,width,fromB,margin]
      · have negative : e≤0 := le_of_not_ge cross
        have order := order_of_cross negative
        rw [minFormula,abs_of_nonpos negative] at axisA
        have hU := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr bLowerU)
        have hV := mul_nonneg dNonneg (show 0≤-B.s+3*B.c-B.side-B.loV by linarith only [vCap])
        have margin := C849SteepMargins.lowerV_a_neg A.c A.s B.c B.s ap.le aq A.unit_normal b
        change 0<1+d-(27/20)*(A.c+A.s)+(13/20)*e*(B.c-B.s) at margin
        have correction : 0≤(3/4)*A.c-(13/20)*A.s := by linarith only [order,ap]
        clear_value d e
        nlinarith only [axisA,hU,hV,vBound,width,fromB,margin,correction]

/-- Original-square bridge: A may have any orientation. R is kept as an
actual disjoint square, including the premises needed to force A through
(2,2.5). The only sector assumption is the stated upper V face of B. -/
theorem impossible (A B R : OpenSquare)
    (bc : 0<B.c) (bs : 0≤B.s) (bsc : B.s≤B.c)
    (same : A.side=B.side) (ha : 1<B.side) (hr : 1<R.side)
    (boxR : InsideContainer R)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : A.Inside (47/20) (47/20))
    (missingF : ¬A.Inside (33/20) (33/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (bT : ClosedInside B (33/20) (47/20)) (bH : B.Inside 2 (1543/500))
    (r₀ : ClosedInside R 3 (12/5)) (r₁ : ClosedInside R (1543/500) 2)
    (rW : ¬R.Inside (81/25) (187/100))
    (ab : ∀ x y, ¬(A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (vCap : B.loV+B.side≤-B.s+3*B.c) : False := by
  have aTclosed : ClosedInside A (47/20) (47/20) :=
    ⟨aT.1.le,aT.2.1.le,aT.2.2.1.le,aT.2.2.2.le⟩
  have aHigh := FourSquareAAll.point A B R (by simpa only [same] using ha) hr boxR
    aP aQ aTclosed missingF missingG bT r₀ r₁ rW ab ar
  have lowB := C849PositiveAbove.b_lower_face B bc bs bT bH (fun h => ab _ _ ⟨aHigh,h⟩)
  have height : B.side≤B.s+B.c/2 := by linarith only [lowB,vCap]
  have outsideB := ClosedPointExclusion.outside_of_closed A B _ _ ab bT
  have outsideR := ClosedPointExclusion.outside_of_closed A R _ _ ar r₀
  obtain ⟨A',ap,aq,side,inside,closed⟩ := ClosedFrames.positive_frame A
  exact in_frame A' B ap aq bc bs bsc (side.trans same) ha height vCap
    ((closed _ _).mpr aP) ((closed _ _).mpr aQ) ((inside _ _).mpr aT)
    (fun h => missingG ((inside _ _).mp h))
    (fun h => outsideB ((inside _ _).mp h))
    (fun h => outsideR ((inside _ _).mp h)) bT bH
    (fun x y h => ab x y ⟨(inside x y).mp h.1,h.2⟩)

#print axioms impossible

end N12Compact.C849SteepAB
