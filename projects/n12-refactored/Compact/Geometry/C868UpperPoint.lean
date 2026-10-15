import Compact.Geometry.C868CentralSeparation
import Compact.Geometry.C868UpperPointMargins

/-! The actual lower-left square and upper central pair cannot both have
positive canonical frames in C868. Their full-square separation forces the
upper square to contain the original top auxiliary point (1.74,3).
This module does not assert the remaining physical orientation sectors. -/
namespace N12Compact.C868UpperPoint

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

theorem point (A H : OpenSquare) (hA : Normal A.c A.s) (hH : Normal H.c H.s)
    (same : A.side=H.side) (side : 1<A.side)
    (aSW : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aQ : A.Inside (87/50) 2)
    (hNW : H.Inside (33/20) (47/20))
    (hNE : H.Inside (47/20) (47/20))
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) :
    H.Inside (87/50) 3 := by
  have ba := normal_bounds hA
  have bh := normal_bounds hH
  have ap : 0<A.c := by linarith only [ba.1]
  have hp : 0<H.c := by linarith only [bh.1]
  have sideH : 1<H.side := by simpa only [same] using side
  have axes := (C868CentralSeparation.positive A H hA hH same side
    aSW aD aQ hNW hNE missingBottom missingLeft apart).1
  let α := H.c*A.c+H.s*A.s
  let β := H.s*A.c-H.c*A.s
  have alphaPos : 0<α := add_pos_of_pos_of_nonneg (mul_pos hp ap)
    (mul_nonneg hH.1 hA.1)
  have wide := mul_pos alphaPos (sub_pos.mpr sideH)
  have betaIdentity : -A.s*H.c+A.c*H.s=β := by dsimp [β]; ring
  have alphaIdentity : -(-A.s)*H.s+A.c*H.c=α := by dsimp [α]; ring
  have lowerPositive (order : 0≤β) :
      lower H (-A.s) A.c=β*H.loU+α*H.loV := by
    rw [lower_in_bands,betaIdentity,alphaIdentity]
    rw [abs_of_nonneg order,abs_of_nonneg alphaPos.le]
    ring
  have lowerNegative (order : β≤0) :
      lower H (-A.s) A.c=β*(H.loU+H.side)+α*H.loV := by
    rw [lower_in_bands,betaIdentity,alphaIdentity]
    rw [abs_of_nonpos order,abs_of_nonneg alphaPos.le]
    ring
  have lowerU : H.loU < H.c*(87/50)+H.s*3 := by
    nlinarith only [hNW.1,hp,hH.1]
  have lowerV : H.loV < -H.s*(87/50)+H.c*3 := by
    nlinarith only [hNE.2.2.1,hp,hH.1]
  have noUpperV (cap : H.loV+H.side ≤ -H.s*(87/50)+H.c*3) : False := by
    rcases axes with axisH | axisA
    · have normal : (-H.s)^2+H.c^2=1 := by nlinarith only [H.unit_normal]
      have lowerPoint := strict_bounds A _ _ (-H.s) H.c normal aQ
      nlinarith only [lowerPoint.2,axisH,cap,sideH,bh.2.1]
    · by_cases order : 0≤β
      · have form := lowerPositive order
        have u := mul_nonneg order (sub_nonneg.mpr hNW.1.le)
        have v := mul_nonneg alphaPos.le (sub_nonneg.mpr cap)
        have margin := C868UpperPointMargins.above hH hA order
        change 0≤α-A.c+β*((9/100)*H.c+(13/20)*H.s) at margin
        have identity : β*(H.c*(33/20)+H.s*(47/20))+
            α*(-H.s*(87/50)+H.c*3) =
            3*A.c-(87/50)*A.s-β*((9/100)*H.c+(13/20)*H.s) := by
          dsimp [α,β]
          linear_combination (3*A.c-(87/50)*A.s)*H.unit_normal
        nlinarith only [axisA,form,u,v,wide,margin,identity,aQ.2.2.2]
      · have negative : β≤0 := le_of_not_ge order
        have form := lowerNegative negative
        have u := mul_nonneg (neg_nonneg.mpr negative)
          (sub_nonneg.mpr hNE.2.1.le)
        have v := mul_nonneg alphaPos.le (sub_nonneg.mpr cap)
        have margin := C868UpperPointMargins.below hH hA negative
        change 0≤α-A.c-β*((61/100)*H.c-(13/20)*H.s) at margin
        have identity : β*(H.c*(47/20)+H.s*(47/20))+
            α*(-H.s*(87/50)+H.c*3) =
            3*A.c-(87/50)*A.s+β*((61/100)*H.c-(13/20)*H.s) := by
          dsimp [α,β]
          linear_combination (3*A.c-(87/50)*A.s)*H.unit_normal
        nlinarith only [axisA,form,u,v,wide,margin,identity,aQ.2.2.2]
  have upperV : -H.s*(87/50)+H.c*3 < H.loV+H.side :=
    lt_of_not_ge noUpperV
  have upperU : H.c*(87/50)+H.s*3 < H.loU+H.side := by
    apply lt_of_not_ge
    intro cap
    have steep : 61*H.c < 65*H.s := by nlinarith only [hNE.2.1,cap]
    rcases axes with axisH | axisA
    · have normal : (-H.s)^2+H.c^2=1 := by nlinarith only [H.unit_normal]
      have bound := strict_bounds A _ _ (-H.s) H.c normal aQ
      nlinarith only [bound.2,axisH,hNE.2.2.1,steep,hp]
    · have normal : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
      have bound := strict_bounds H _ _ (-A.s) A.c normal hNE
      have shallow : 61*A.s < 35*A.c := by
        nlinarith only [axisA,bound.1,aQ.2.2.2]
      have hSlope : 9*H.c≤10*H.s := by linarith only [steep,hp]
      have aSlope : 5*A.s≤3*A.c := by linarith only [shallow,ap]
      have first := mul_nonneg ap.le (sub_nonneg.mpr hSlope)
      have second := mul_nonneg hp.le (sub_nonneg.mpr aSlope)
      have positive := mul_pos hp ap
      have order : 0<β := by dsimp [β]; nlinarith only [first,second,positive]
      have form := lowerPositive order.le
      have u := mul_nonneg order.le (sub_nonneg.mpr cap)
      have v := mul_nonneg alphaPos.le (sub_nonneg.mpr hNE.2.2.1.le)
      have narrow := mul_pos order (sub_pos.mpr sideH)
      have margin := C868UpperPointMargins.steep hH hA steep.le shallow.le
      have identity :
          (2*A.c-(87/50)*A.s)-
          (β*(H.c*(87/50)+H.s*3-1)+α*(-H.s*(47/20)+H.c*(47/20))) =
          A.c*(H.s-7/20-(13/20)*H.s^2+(61/100)*H.c*H.s)+
          A.s*((61/100)*H.s^2+(13/20)*H.c*H.s-H.c) := by
        dsimp [α,β]
        linear_combination (-(47/20)*A.c+(87/50)*A.s)*H.unit_normal
      nlinarith only [axisA,form,u,v,narrow,margin,identity,aQ.2.2.2]
  exact ⟨lowerU,upperU,lowerV,upperV⟩

end N12Compact.C868UpperPoint
