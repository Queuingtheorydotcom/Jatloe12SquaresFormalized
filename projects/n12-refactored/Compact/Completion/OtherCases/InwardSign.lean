import Compact.Completion.OtherCases.InwardSignSupports

/-! Complete continuous inward-sign theorem. Every orientation of the
western square and all forward/reverse actual SAT face axes are covered. -/
namespace N12Compact.Completion.OtherCases.InwardSign
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem positive_impossible (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side) (cp : 0<E.c) (sn : 0≤E.s) (order : E.s≤E.c)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (upperInward : W.Inside 0 (13/50))
    (marker : E.Inside (7/20) (-7/20)) (inner : E.Inside 0 (-13/50))
    (elbow : E.Inside (13/50) 0) (missingF : ¬E.Inside 1 (-13/50))
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : False := by
  have cu := (CommonCases.CanonicalScalars.bounds E.c E.s cp sn order E.unit_normal).2.1
  have hCap : E.loV+E.side≤0 := by
    apply le_of_not_gt
    intro high
    apply apart 0 0
    refine ⟨center,?_⟩
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero,zero_add]
    refine ⟨?_,?_,?_,high⟩ <;> linarith only [inner.1,elbow.2.1,marker.2.2.1,cp,sn]
  have sp : 0<E.s := by linarith only [elbow.2.2.2,hCap]
  have fLowU : E.loU<E.c-E.s*(13/50) := by linarith only [inner.1,cp]
  have fHighV : -E.s-E.c*(13/50)<E.loV+E.side := by
    linarith only [elbow.2.2.2,cp,sn]
  have short := CommonCases.OutwardScalars.increasing_projection E.c E.s (13/50) 1
    cp sn order E.unit_normal (by norm_num) (by norm_num) (by norm_num)
  have fLowV : E.loV< -E.s-E.c*(13/50) := by linarith only [hCap,side,short]
  have aCap : E.loU+E.side≤E.c-(13/50)*E.s := by
    apply le_of_not_gt
    intro high
    exact missingF (by
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro fLowU (And.intro (by linarith only [high]) (And.intro fLowV fHighV)))
  have lastLowU : E.loU<(4/5)*E.c-E.s := by
    linarith only [inner.1,cp,order]
  have bar := BottomBarSupport.positive E side cp sn cu elbow lastLowU avoid
  have data : InwardSignSupports.Data E := ⟨cp,sp,order,side,aCap,hCap,bar⟩
  obtain ⟨w,wp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame W
  have p := (inside _ _).mpr west
  have o := (inside _ _).mpr center
  have f := (inside _ _).mpr upperInward
  have same' : w.side=E.side := shape.trans same
  have disjoint : ∀ x y,¬(w.Inside x y ∧ E.Inside x y) :=
    fun x y own => apart x y ⟨(inside _ _).mp own.1,own.2⟩
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper w nx ny≤lower E nx ny) : 0<nx ∧ ny<0 := by
    have first := (strict_bounds w _ _ nx ny unit p).2
    have last := (strict_bounds E _ _ nx ny unit marker).1
    have firstY := (strict_bounds w _ _ nx ny unit f).2
    have lastY := (strict_bounds E _ _ nx ny unit inner).1
    constructor <;> linarith only [first,last,firstY,lastY,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower w nx ny) :
      upper w (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have bounds := abs_le.mp range
  have noWU (sep : upper w w.c w.s≤lower E w.c w.s ∨
      upper E w.c w.s≤lower w w.c w.s) : False := by
    rcases sep with forward | backward
    · by_cases sign : 0≤w.s
      · have signCone := cone w.c w.s w.unit_normal forward
        linarith only [signCone.2,sign]
      · exact InwardSignSupports.negative_w_axis w E (-w.s) (by ring) wp
          (by linarith only [sign]) (by linarith only [bounds.1]) data o forward
    · have signCone := cone (-w.c) (-w.s)
        (by simpa only [neg_sq] using w.unit_normal) (reverse _ _ backward)
      linarith only [signCone.1,wp]
  have noWV (sep : upper w (-w.s) w.c≤lower E (-w.s) w.c ∨
      upper E (-w.s) w.c≤lower w (-w.s) w.c) : False := by
    have unit : (-w.s)^2+w.c^2=1 := by nlinarith only [w.unit_normal]
    rcases sep with forward | backward
    · have signCone := cone (-w.s) w.c unit forward
      linarith only [signCone.2,wp]
    · have opposite : upper w w.s (-w.c)≤lower E w.s (-w.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      by_cases sign : 0≤w.s
      · exact InwardSignSupports.positive_w_axis w E wp sign bounds.2 data p elbow opposite
      · have signCone := cone w.s (-w.c) (by nlinarith only [w.unit_normal]) opposite
        linarith only [signCone.1,sign]
  have noEU (sep : upper w E.c E.s≤lower E E.c E.s ∨
      upper E E.c E.s≤lower w E.c E.s) : False := by
    rcases sep with forward | backward
    · have signCone := cone E.c E.s E.unit_normal forward
      linarith only [signCone.2,sp]
    · have signCone := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [signCone.1,cp]
  have noEV (sep : upper w (-E.s) E.c≤lower E (-E.s) E.c ∨
      upper E (-E.s) E.c≤lower w (-E.s) E.c) : False := by
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    rcases sep with forward | backward
    · have signCone := cone (-E.s) E.c unit forward
      linarith only [signCone.1,sp]
    · apply InwardSignSupports.own_axis w E data p
      simpa only [neg_neg] using reverse _ _ backward
  have axes := CongruentSAT.faceSeparation_of_disjoint w E same' disjoint
  change pairRadius w E≤|w.c*(centerX E-centerX w)+w.s*(centerY E-centerY w)| ∨
    pairRadius w E≤|-w.s*(centerX E-centerX w)+w.c*(centerY E-centerY w)| ∨
    pairRadius E w≤|E.c*(centerX E-centerX w)+E.s*(centerY E-centerY w)| ∨
    pairRadius E w≤|-E.s*(centerX E-centerX w)+E.c*(centerY E-centerY w)| at axes
  have separate (nx ny R : ℝ)
      (radius : supportRadius w nx ny+supportRadius E nx ny=R)
      (axis : R≤|nx*(centerX E-centerX w)+ny*(centerY E-centerY w)|) :=
    separated w E nx ny (by rwa [radius])
  rcases axes with wu | wv | eu | ev
  · exact noWU (separate _ _ _ (parallel_radius w E) wu)
  · exact noWV (separate _ _ _ (transverse_radius w E) wv)
  · have radius : supportRadius w E.c E.s+supportRadius E E.c E.s=pairRadius E w := by
      rw [add_comm]
      exact parallel_radius E w
    exact noEU (separate _ _ _ radius eu)
  · have radius : supportRadius w (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E w := by
      rw [add_comm]
      exact transverse_radius E w
    exact noEV (separate _ _ _ radius ev)

/-- The inward southeast owner with an omitted F8 must have negative
canonical sine; every western orientation and every normal has been kept. -/
theorem canonical_negative (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side) (cp : 0<E.c) (range : |E.s|≤E.c)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (upperInward : W.Inside 0 (13/50))
    (marker : E.Inside (7/20) (-7/20)) (inner : E.Inside 0 (-13/50))
    (elbow : E.Inside (13/50) 0) (missingF : ¬E.Inside 1 (-13/50))
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : E.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  exact positive_impossible W E side same cp nonnegative (abs_le.mp range).2
    west center upperInward marker inner elbow missingF avoid apart

#print axioms positive_impossible
#print axioms canonical_negative
end N12Compact.Completion.OtherCases.InwardSign

