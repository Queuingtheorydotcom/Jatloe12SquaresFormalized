import Compact.Geometry.ABTransverse

/-! The actual left wall square lies above a central square owning (1,2)
on one of their two transverse axes. Positive face frames span the whole
first quadrant, so no small-angle or wall-orientation restriction occurs. -/
namespace N12Compact.CentralLeftWallSeparation

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

theorem alternatives (A W : OpenSquare)
    (ac : 0<A.c) (as_ : 0≤A.s) (wc : 0<W.c) (ws : 0≤W.s)
    (same : A.side=W.side)
    (aPoint : A.Inside 1 2)
    (wMarker : W.Inside (457/500) 2) (wF : W.Inside 1 (113/50))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    A.loV+A.side ≤ lower W (-A.s) A.c ∨
      upper A (-W.s) W.c ≤ W.loV := by
  have longitudinal (c s : ℝ) (hc : 0<c) (hs : 0≤s) (unit : c^2+s^2=1) :
      ¬ (upper A c s ≤ lower W c s ∨ upper W c s ≤ lower A c s) := by
    have a := strict_bounds A _ _ c s unit aPoint
    have m := strict_bounds W _ _ c s unit wMarker
    have f := strict_bounds W _ _ c s unit wF
    rintro (forward | backward)
    · nlinarith only [forward,a.2,m.1,hc]
    · nlinarith only [backward,f.2,a.1,hs]
  have reverse (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1) :
      ¬ upper W (-s) c ≤ lower A (-s) c := by
    have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
    have a := strict_bounds A _ _ (-s) c vunit aPoint
    have f := strict_bounds W _ _ (-s) c vunit wF
    intro backward
    nlinarith only [backward,f.2,a.1,hc]
  have axes := CongruentSAT.faceSeparation_of_disjoint A W same apart
  change pairRadius A W ≤ |A.c*(centerX W-centerX A)+A.s*(centerY W-centerY A)| ∨
    pairRadius A W ≤ |-A.s*(centerX W-centerX A)+A.c*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |W.c*(centerX W-centerX A)+W.s*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |-W.s*(centerX W-centerX A)+W.c*(centerY W-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX A)+ny*(centerY W-centerY A)|) :=
    separated A W nx ny (by rwa [identity])
  rcases axes with au | av | wu | wv
  · exact False.elim (longitudinal A.c A.s ac as_ A.unit_normal
      (separateAxis _ _ _ (parallel_radius A W) au))
  · have sep := separateAxis _ _ _ (transverse_radius A W) av
    rcases sep with sep | sep
    · left; simpa only [(ownV A).2] using sep
    · exact False.elim (reverse A.c A.s ac A.unit_normal sep)
  · have identity : supportRadius A W.c W.s+supportRadius W W.c W.s=pairRadius W A := by
      rw [add_comm]; exact parallel_radius W A
    exact False.elim (longitudinal W.c W.s wc ws W.unit_normal
      (separateAxis _ _ _ identity wu))
  · have identity : supportRadius A (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W A := by
      rw [add_comm]; exact transverse_radius W A
    have sep := separateAxis _ _ _ identity wv
    rcases sep with sep | sep
    · right; simpa only [(ownV W).1] using sep
    · exact False.elim (reverse W.c W.s wc W.unit_normal sep)

/-- In a negative frame of W the second transverse alternative is its
own U face, directed from W toward A. No strict wall tilt is required. -/
theorem negative_alternatives (A W : OpenSquare)
    (ac : 0<A.c) (as_ : 0≤A.s) (wc : 0<W.c) (ws : W.s≤0)
    (same : A.side=W.side)
    (aPoint : A.Inside 1 2)
    (wMarker : W.Inside (457/500) 2) (wF : W.Inside 1 (113/50))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    A.loV+A.side ≤ lower W (-A.s) A.c ∨
      W.loU+W.side ≤ lower A W.c W.s := by
  have au : ¬ (upper A A.c A.s≤lower W A.c A.s ∨
      upper W A.c A.s≤lower A A.c A.s) := by
    have a := strict_bounds A _ _ A.c A.s A.unit_normal aPoint
    have m := strict_bounds W _ _ A.c A.s A.unit_normal wMarker
    have f := strict_bounds W _ _ A.c A.s A.unit_normal wF
    rintro (h | h) <;> nlinarith only [h,a.1,a.2,m.1,f.2,ac,as_]
  have av : ¬ upper W (-A.s) A.c≤lower A (-A.s) A.c := by
    have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    have a := strict_bounds A _ _ (-A.s) A.c unit aPoint
    have f := strict_bounds W _ _ (-A.s) A.c unit wF
    intro h
    nlinarith only [h,a.1,f.2,ac]
  have wu : ¬ upper A W.c W.s≤lower W W.c W.s := by
    have a := strict_bounds A _ _ W.c W.s W.unit_normal aPoint
    have m := strict_bounds W _ _ W.c W.s W.unit_normal wMarker
    intro h
    nlinarith only [h,a.2,m.1,wc]
  have wv : ¬ (upper A (-W.s) W.c≤lower W (-W.s) W.c ∨
      upper W (-W.s) W.c≤lower A (-W.s) W.c) := by
    have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have a := strict_bounds A _ _ (-W.s) W.c unit aPoint
    have m := strict_bounds W _ _ (-W.s) W.c unit wMarker
    have f := strict_bounds W _ _ (-W.s) W.c unit wF
    rintro (h | h) <;> nlinarith only [h,a.1,a.2,m.1,f.2,wc,ws]
  have axes := CongruentSAT.faceSeparation_of_disjoint A W same apart
  change pairRadius A W ≤ |A.c*(centerX W-centerX A)+A.s*(centerY W-centerY A)| ∨
    pairRadius A W ≤ |-A.s*(centerX W-centerX A)+A.c*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |W.c*(centerX W-centerX A)+W.s*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |-W.s*(centerX W-centerX A)+W.c*(centerY W-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX A)+ny*(centerY W-centerY A)|) :=
    separated A W nx ny (by rwa [identity])
  rcases axes with sep | sep | sep | sep
  · exact False.elim (au (separateAxis _ _ _ (parallel_radius A W) sep))
  · rcases separateAxis _ _ _ (transverse_radius A W) sep with h | h
    · left; simpa only [(ownV A).2] using h
    · exact False.elim (av h)
  · have identity : supportRadius A W.c W.s+supportRadius W W.c W.s=pairRadius W A := by
      rw [add_comm]; exact parallel_radius W A
    rcases separateAxis _ _ _ identity sep with h | h
    · exact False.elim (wu h)
    · right; simpa only [(ownU W).2] using h
  · have identity : supportRadius A (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W A := by
      rw [add_comm]; exact transverse_radius W A
    exact False.elim (wv (separateAxis _ _ _ identity sep))

end N12Compact.CentralLeftWallSeparation
