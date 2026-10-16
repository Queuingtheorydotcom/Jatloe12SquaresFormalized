import Compact.Geometry.C868CentralSupport

/-! Exact separating-axis reduction for the lower-left square and the
upper central pair. The support bounds are supplied by CentralSupport;
the reverse orientations of all four axes are excluded by original points.
No transverse alternative is discarded by a sampled-angle assertion. -/
namespace N12Compact.C868CentralSeparation

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

theorem alternatives (A H : OpenSquare)
    (ac : 0 < A.c) (aLower : -A.c ≤ A.s) (ao : A.s ≤ A.c)
    (hc : 0 < H.c) (hLower : -H.c ≤ H.s) (ho : H.s ≤ H.c)
    (same : A.side=H.side)
    (aSW : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50))
    (hNW : H.Inside (33/20) (47/20))
    (hNE : H.Inside (47/20) (47/20))
    (supportA : (33/20)*A.c+(47/20)*A.s < upper A A.c A.s)
    (supportH : (33/20)*H.c+(47/20)*H.s < upper A H.c H.s)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) :
    upper A (-H.s) H.c ≤ H.loV ∨
      A.loV+A.side ≤ lower H (-A.s) A.c := by
  have longitudinal (c s : ℝ) (cp : 0<c) (sp : -c≤s)
      (unit : c^2+s^2=1)
      (bound : (33/20)*c+(47/20)*s < upper A c s) :
      ¬ (upper A c s ≤ lower H c s ∨ upper H c s ≤ lower A c s) := by
    have nw := strict_bounds H _ _ c s unit hNW
    have ne := strict_bounds H _ _ c s unit hNE
    have ad := strict_bounds A _ _ c s unit aSW
    rintro (sep | sep)
    · nlinarith only [bound,nw.1,sep]
    · nlinarith only [ne.2,ad.1,sep,cp,sp]
  have reverse (c s : ℝ) (cp : 0<c) (order : s≤c)
      (unit : c^2+s^2=1) :
      ¬ upper H (-s) c ≤ lower A (-s) c := by
    have unit' : (-s)^2+c^2=1 := by nlinarith only [unit]
    have ne := strict_bounds H _ _ (-s) c unit' hNE
    have sw := strict_bounds A _ _ (-s) c unit' aSW
    intro sep
    nlinarith only [ne.2,sw.1,sep,order]
  have axes := CongruentSAT.faceSeparation_of_disjoint A H same apart
  change pairRadius A H ≤ |A.c*(centerX H-centerX A)+A.s*(centerY H-centerY A)| ∨
    pairRadius A H ≤ |-A.s*(centerX H-centerX A)+A.c*(centerY H-centerY A)| ∨
    pairRadius H A ≤ |H.c*(centerX H-centerX A)+H.s*(centerY H-centerY A)| ∨
    pairRadius H A ≤ |-H.s*(centerX H-centerX A)+H.c*(centerY H-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius H nx ny=R)
      (sep : R≤|nx*(centerX H-centerX A)+ny*(centerY H-centerY A)|) :=
    separated A H nx ny (by rwa [identity])
  rcases axes with au | av | hu | hv
  · exact False.elim (longitudinal A.c A.s ac aLower A.unit_normal supportA
      (separateAxis _ _ _ (parallel_radius A H) au))
  · have sep := separateAxis _ _ _ (transverse_radius A H) av
    rcases sep with sep | sep
    · right; simpa only [(ownV A).2] using sep
    · exact False.elim (reverse A.c A.s ac ao A.unit_normal sep)
  · have identity : supportRadius A H.c H.s+supportRadius H H.c H.s=pairRadius H A := by
      rw [add_comm]; exact parallel_radius H A
    exact False.elim (longitudinal H.c H.s hc hLower H.unit_normal supportH
      (separateAxis _ _ _ identity hu))
  · have identity : supportRadius A (-H.s) H.c+supportRadius H (-H.s) H.c=pairRadius H A := by
      rw [add_comm]; exact transverse_radius H A
    have sep := separateAxis _ _ _ identity hv
    rcases sep with sep | sep
    · left; simpa only [(ownV H).1] using sep
    · exact False.elim (reverse H.c H.s hc ho H.unit_normal sep)

/-- Each surviving transverse separation restricts the angle of the square
whose own transverse face is used. The other square's angle is not bounded
by this argument. -/
theorem transverse_orders (A H : OpenSquare)
    (aQ : A.Inside (87/50) 2) (hNE : H.Inside (47/20) (47/20))
    (separation : upper A (-H.s) H.c ≤ H.loV ∨
      A.loV+A.side ≤ lower H (-A.s) A.c) :
    61*H.s < 35*H.c ∨ 61*A.s < 35*A.c := by
  rcases separation with h | h
  · have unit : (-H.s)^2+H.c^2=1 := by nlinarith only [H.unit_normal]
    have bound := strict_bounds A _ _ (-H.s) H.c unit aQ
    left; nlinarith only [bound.2,h,hNE.2.2.1]
  · have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    have bound := strict_bounds H _ _ (-A.s) A.c unit hNE
    right; nlinarith only [aQ.2.2.2,h,bound.1]

/-- The support premises of `alternatives` follow from the actual lower
square and its two foreign auxiliary points. -/
theorem positive (A H : OpenSquare)
    (hA : C977CornerCubic.Normal A.c A.s)
    (hH : C977CornerCubic.Normal H.c H.s)
    (same : A.side=H.side) (side : 1<A.side)
    (aSW : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aQ : A.Inside (87/50) 2)
    (hNW : H.Inside (33/20) (47/20))
    (hNE : H.Inside (47/20) (47/20))
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) :
    (upper A (-H.s) H.c ≤ H.loV ∨
      A.loV+A.side ≤ lower H (-A.s) A.c) ∧
      (61*H.s < 35*H.c ∨ 61*A.s < 35*A.c) := by
  have ba := C977CornerCubic.normal_bounds hA
  have bh := C977CornerCubic.normal_bounds hH
  have supportA := C868CentralSupport.positive_support A A.c A.s hA hA side
    aSW aD aQ missingBottom missingLeft
  have supportH := C868CentralSupport.positive_support A H.c H.s hH hA side
    aSW aD aQ missingBottom missingLeft
  have result := alternatives A H (by linarith only [ba.1])
    (by linarith only [ba.1,hA.1]) hA.2.1
    (by linarith only [bh.1]) (by linarith only [bh.1,hH.1]) hH.2.1 same aSW aD hNW hNE
    supportA supportH apart
  exact ⟨result,transverse_orders A H aQ hNE result⟩

/-- In the negative lower-square sector, the centre is supplied by the
existing actual-singleton corner theorem. It gives the required support
without assuming the false positive-central centre assertion. -/
theorem negative (A H : OpenSquare)
    (hA : C977CornerCubic.Normal A.c (-A.s))
    (hH : C977CornerCubic.Normal H.c H.s)
    (same : A.side=H.side)
    (aSW : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (centre : A.Inside 2 2)
    (hNW : H.Inside (33/20) (47/20))
    (hNE : H.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ H.Inside x y)) :
    upper A (-H.s) H.c ≤ H.loV ∨
      A.loV+A.side ≤ lower H (-A.s) A.c := by
  have ba := C977CornerCubic.normal_bounds hA
  have bh := C977CornerCubic.normal_bounds hH
  have ad := strict_bounds A _ _ A.c A.s A.unit_normal aD
  have mid := strict_bounds A _ _ H.c H.s H.unit_normal centre
  have supportA : (33/20)*A.c+(47/20)*A.s < upper A A.c A.s := by
    nlinarith only [ad.2,ba.1,hA.1]
  have supportH : (33/20)*H.c+(47/20)*H.s < upper A H.c H.s := by
    nlinarith only [mid.2,hH.2.1]
  exact alternatives A H (by linarith only [ba.1])
    (by linarith only [hA.2.1]) (by linarith only [ba.1,hA.1])
    (by linarith only [bh.1]) (by linarith only [bh.1,hH.1]) hH.2.1
    same aSW aD hNW hNE supportA supportH apart

end N12Compact.C868CentralSeparation
