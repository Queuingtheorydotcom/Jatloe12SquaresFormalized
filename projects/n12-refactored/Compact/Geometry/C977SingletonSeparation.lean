import Compact.Geometry.ABTransverse

/-! A genuine tilted-face restriction from a bottom singleton and the
southwest central square. The negative canonical sectors are explicit
hypotheses; this module does not establish their C977 coverage. -/
namespace N12Compact.C977SingletonSeparation

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

/-- Two owned points on each actual square rule out both longitudinal
axes and the reverse transverse directions. Boundary contact is retained
in the two remaining weak inequalities. -/
theorem bottom_alternatives (O A : OpenSquare)
    (oc : 0 < O.c) (os : O.s ≤ 0) (ot : -O.c ≤ O.s)
    (ac : 0 < A.c) (as_ : A.s ≤ 0) (aTilt : -A.c ≤ A.s)
    (same : O.side = A.side)
    (oN : O.Inside (28/25) 1)
    (oL : O.Inside (187/100) (19/25))
    (aP : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50))
    (apart : ∀ x y, ¬ (O.Inside x y ∧ A.Inside x y)) :
    O.loV + O.side ≤ lower A (-O.s) O.c ∨
      upper O (-A.s) A.c ≤ A.loV := by
  have longitudinal (c s : ℝ) (hc : 0 < c) (hs : s ≤ 0)
      (ht : -c ≤ s) (hn : c^2+s^2=1) :
      ¬ (upper O c s ≤ lower A c s ∨ upper A c s ≤ lower O c s) := by
    have oL' := strict_bounds O _ _ c s hn oL
    have aP' := strict_bounds A _ _ c s hn aP
    have oN' := strict_bounds O _ _ c s hn oN
    have aD' := strict_bounds A _ _ c s hn aD
    rintro (sep | sep)
    · nlinarith only [sep, oL'.2, aP'.1, hc, hs]
    · nlinarith only [sep, aD'.2, oN'.1, hc, ht]
  have reverse (c s : ℝ) (hc : 0 < c) (hs : s ≤ 0)
      (hn : c^2+s^2=1) : ¬ upper A (-s) c ≤ lower O (-s) c := by
    have unit : (-s)^2+c^2=1 := by nlinarith only [hn]
    have aP' := strict_bounds A _ _ (-s) c unit aP
    have oN' := strict_bounds O _ _ (-s) c unit oN
    intro sep
    nlinarith only [sep, aP'.2, oN'.1, hc, hs]
  have axes := CongruentSAT.faceSeparation_of_disjoint O A same apart
  change pairRadius O A ≤ |O.c*(centerX A-centerX O)+O.s*(centerY A-centerY O)| ∨
    pairRadius O A ≤ |-O.s*(centerX A-centerX O)+O.c*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |A.c*(centerX A-centerX O)+A.s*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |-A.s*(centerX A-centerX O)+A.c*(centerY A-centerY O)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius O nx ny+supportRadius A nx ny=R)
      (sep : R ≤ |nx*(centerX A-centerX O)+ny*(centerY A-centerY O)|) :=
    separated O A nx ny (by rwa [identity])
  rcases axes with ou | ov | au | av
  · exact False.elim (longitudinal O.c O.s oc os ot O.unit_normal
      (separateAxis O.c O.s _ (parallel_radius O A) ou))
  · have sep := separateAxis (-O.s) O.c _ (transverse_radius O A) ov
    rcases sep with sep | sep
    · left; simpa only [(ownV O).2] using sep
    · exact False.elim (reverse O.c O.s oc os O.unit_normal sep)
  · have identity : supportRadius O A.c A.s+supportRadius A A.c A.s=pairRadius A O := by
      rw [add_comm]; exact parallel_radius A O
    exact False.elim (longitudinal A.c A.s ac as_ aTilt A.unit_normal
      (separateAxis A.c A.s _ identity au))
  · have identity : supportRadius O (-A.s) A.c+supportRadius A (-A.s) A.c=pairRadius A O := by
      rw [add_comm]; exact transverse_radius A O
    have sep := separateAxis (-A.s) A.c _ identity av
    rcases sep with sep | sep
    · right; simpa only [(ownV A).1] using sep
    · exact False.elim (reverse A.c A.s ac as_ A.unit_normal sep)

end N12Compact.C977SingletonSeparation
