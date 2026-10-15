import Compact.Geometry.C868UpperPoint

/-! The negative lower-square sector uses the strict centre point supplied
by the actual bottom/left-singleton theorem. The upper central frame is
still positive; its negative physical orientation remains a separate case. -/
namespace N12Compact.C868UpperPointNegative

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

theorem point (A H : OpenSquare) (hA : Normal A.c (-A.s))
    (hH : Normal H.c H.s) (same : A.side=H.side) (side : 1<A.side)
    (aSW : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aQ : A.Inside (87/50) 2)
    (centre : A.Inside 2 2)
    (hNW : H.Inside (33/20) (47/20))
    (hNE : H.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) :
    H.Inside (87/50) 3 := by
  have ba := normal_bounds hA
  have bh := normal_bounds hH
  have ap : 0<A.c := by linarith only [ba.1]
  have hp : 0<H.c := by linarith only [bh.1]
  have sideH : 1<H.side := by simpa only [same] using side
  have axes := C868CentralSeparation.negative A H hA hH same aSW aD centre hNW hNE apart
  let α := H.c*A.c+H.s*A.s
  let β := H.s*A.c-H.c*A.s
  have alphaNonneg : 0≤α := by
    have first := mul_nonneg hp.le (show 0≤A.c+A.s by linarith only [hA.2.1])
    have second := mul_nonneg hA.1 (sub_nonneg.mpr hH.2.1)
    dsimp [α]; nlinarith only [first,second]
  have betaNonneg : 0≤β := by
    have first := mul_nonneg hH.1 ap.le
    have second := mul_nonneg hp.le hA.1
    dsimp [β]; nlinarith only [first,second]
  have wide := mul_nonneg alphaNonneg (sub_nonneg.mpr sideH.le)
  have narrow := mul_nonneg betaNonneg (sub_nonneg.mpr sideH.le)
  have betaIdentity : -A.s*H.c+A.c*H.s=β := by dsimp [β]; ring
  have alphaIdentity : -(-A.s)*H.s+A.c*H.c=α := by dsimp [α]; ring
  have formula : lower H (-A.s) A.c=β*H.loU+α*H.loV := by
    rw [lower_in_bands,betaIdentity,alphaIdentity,
      abs_of_nonneg betaNonneg,abs_of_nonneg alphaNonneg]
    ring
  have lowerU : H.loU < H.c*(87/50)+H.s*3 := by
    nlinarith only [hNW.1,hp,hH.1]
  have lowerV : H.loV < -H.s*(87/50)+H.c*3 := by
    nlinarith only [hNE.2.2.1,hp,hH.1]
  have upperV : -H.s*(87/50)+H.c*3 < H.loV+H.side := by
    apply lt_of_not_ge
    intro cap
    rcases axes with axisH | axisA
    · have normal : (-H.s)^2+H.c^2=1 := by nlinarith only [H.unit_normal]
      have bound := strict_bounds A _ _ (-H.s) H.c normal aQ
      nlinarith only [bound.2,axisH,cap,sideH,bh.2.1]
    · have u := mul_nonneg betaNonneg (sub_nonneg.mpr hNW.1.le)
      have v := mul_nonneg alphaNonneg (sub_nonneg.mpr cap)
      have margin := C868UpperPointMargins.negative_above hH hA
      have identity : β*(H.c*(33/20)+H.s*(47/20))+
          α*(-H.s*(87/50)+H.c*3) =
          3*A.c-(87/50)*A.s-β*((9/100)*H.c+(13/20)*H.s) := by
        dsimp [α,β]
        linear_combination (3*A.c-(87/50)*A.s)*H.unit_normal
      have normalized : 0≤α-A.c-(13/50)*A.s+
          β*((9/100)*H.c+(13/20)*H.s) := by
        dsimp [α,β]
        nlinarith only [margin]
      nlinarith only [axisA,formula,u,v,wide,normalized,identity,centre.2.2.2]
  have upperU : H.c*(87/50)+H.s*3 < H.loU+H.side := by
    apply lt_of_not_ge
    intro cap
    have steep : 61*H.c < 65*H.s := by nlinarith only [hNE.2.1,cap]
    rcases axes with axisH | axisA
    · have normal : (-H.s)^2+H.c^2=1 := by nlinarith only [H.unit_normal]
      have bound := strict_bounds A _ _ (-H.s) H.c normal aQ
      nlinarith only [bound.2,axisH,hNE.2.2.1,steep,hp]
    · have u := mul_nonneg betaNonneg (sub_nonneg.mpr cap)
      have v := mul_nonneg alphaNonneg (sub_nonneg.mpr hNE.2.2.1.le)
      have margin := C868UpperPointMargins.negative_steep hH hA steep.le
      have identity :
          (2*A.c-2*A.s)-
          (β*(H.c*(87/50)+H.s*3-1)+α*(-H.s*(47/20)+H.c*(47/20))) =
          A.c*(H.s-7/20-(13/20)*H.s^2+(61/100)*H.c*H.s)+
          (-A.s)*((13/50)-((61/100)*H.s^2+(13/20)*H.c*H.s-H.c)) := by
        dsimp [α,β]
        linear_combination (-(47/20)*A.c+(87/50)*A.s)*H.unit_normal
      nlinarith only [axisA,formula,u,v,narrow,margin,identity,centre.2.2.2]
  exact ⟨lowerU,upperU,lowerV,upperV⟩

end N12Compact.C868UpperPointNegative
