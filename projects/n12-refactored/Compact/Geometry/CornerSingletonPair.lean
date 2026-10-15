import Compact.Geometry.ABTransverse

/-! The actual two corner singletons have only one possible directed
separating axis per signed frame when the left singleton owns (1,1).
No container wall, numerical angle interval, or central-square enclosure
enters this reduction. Weak support separation permits boundary contact. -/
namespace N12Compact.CornerSingletonPair

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

def Directed (O L : OpenSquare) (c s : ℝ) : Prop :=
  (0 ≤ s ∧ upper O (-s) c ≤ lower L (-s) c) ∨
    (s < 0 ∧ upper L c s ≤ lower O c s)

/-- Positive frames force bottom-before-left transverse separation;
negative frames force left-before-bottom longitudinal separation. -/
theorem alternatives (O L : OpenSquare) (oc : 0 < O.c) (lc : 0 < L.c)
    (same : O.side=L.side)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25))
    (corner : L.Inside 1 1)
    (apart : ∀ x y, ¬ (O.Inside x y ∧ L.Inside x y)) :
    Directed O L O.c O.s ∨ Directed O L L.c L.s := by
  have fromU (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper O c s ≤ lower L c s ∨ upper L c s ≤ lower O c s) :
      Directed O L c s := by
    have m := strict_bounds O _ _ c s unit oM
    have n := strict_bounds O _ _ c s unit oN
    have f := strict_bounds O _ _ c s unit oF
    have k := strict_bounds L _ _ c s unit corner
    by_cases sign : 0≤s
    · exfalso
      rcases sep with forward | backward
      · nlinarith only [forward,n.2,k.1,hc]
      · nlinarith only [backward,k.2,m.1,sign]
    · right
      have negative : s<0 := lt_of_not_ge sign
      refine ⟨negative,?_⟩
      rcases sep with forward | backward
      · exfalso
        nlinarith only [forward,f.2,k.1,hc,negative]
      · exact backward
  have fromV (c s : ℝ) (hc : 0<c) (unit : c^2+s^2=1)
      (sep : upper O (-s) c ≤ lower L (-s) c ∨
        upper L (-s) c ≤ lower O (-s) c) : Directed O L c s := by
    have vunit : (-s)^2+c^2=1 := by nlinarith only [unit]
    have m := strict_bounds O _ _ (-s) c vunit oM
    have n := strict_bounds O _ _ (-s) c vunit oN
    have k := strict_bounds L _ _ (-s) c vunit corner
    by_cases sign : 0≤s
    · left
      refine ⟨sign,?_⟩
      rcases sep with forward | backward
      · exact forward
      · exfalso
        nlinarith only [backward,k.2,m.1,hc]
    · exfalso
      have negative : s<0 := lt_of_not_ge sign
      rcases sep with forward | backward
      · nlinarith only [forward,n.2,k.1,negative]
      · nlinarith only [backward,k.2,m.1,hc]
  have axes := CongruentSAT.faceSeparation_of_disjoint O L same apart
  change pairRadius O L ≤ |O.c*(centerX L-centerX O)+O.s*(centerY L-centerY O)| ∨
    pairRadius O L ≤ |-O.s*(centerX L-centerX O)+O.c*(centerY L-centerY O)| ∨
    pairRadius L O ≤ |L.c*(centerX L-centerX O)+L.s*(centerY L-centerY O)| ∨
    pairRadius L O ≤ |-L.s*(centerX L-centerX O)+L.c*(centerY L-centerY O)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius O nx ny+supportRadius L nx ny=R)
      (sep : R ≤ |nx*(centerX L-centerX O)+ny*(centerY L-centerY O)|) :=
    separated O L nx ny (by rwa [identity])
  rcases axes with ou | ov | lu | lv
  · exact Or.inl (fromU O.c O.s oc O.unit_normal
      (separateAxis _ _ _ (parallel_radius O L) ou))
  · exact Or.inl (fromV O.c O.s oc O.unit_normal
      (separateAxis _ _ _ (transverse_radius O L) ov))
  · have identity : supportRadius O L.c L.s+supportRadius L L.c L.s=pairRadius L O := by
      rw [add_comm]; exact parallel_radius L O
    exact Or.inr (fromU L.c L.s lc L.unit_normal (separateAxis _ _ _ identity lu))
  · have identity : supportRadius O (-L.s) L.c+supportRadius L (-L.s) L.c=pairRadius L O := by
      rw [add_comm]; exact transverse_radius L O
    exact Or.inr (fromV L.c L.s lc L.unit_normal (separateAxis _ _ _ identity lv))

/-- In positive normal frames the two alternatives are both transverse,
with the bottom singleton below the left singleton. These frames may span
the whole first quadrant, not only the canonical half quadrant. -/
theorem positive_alternatives (O L : OpenSquare)
    (oc : 0<O.c) (os : 0≤O.s) (lc : 0<L.c) (ls : 0≤L.s)
    (same : O.side=L.side)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25)) (corner : L.Inside 1 1)
    (apart : ∀ x y, ¬ (O.Inside x y ∧ L.Inside x y)) :
    O.loV+O.side ≤ lower L (-O.s) O.c ∨
      upper O (-L.s) L.c ≤ L.loV := by
  rcases alternatives O L oc lc same oM oN oF corner apart with h | h
  · rcases h with h | h
    · exact Or.inl (by simpa only [(ownV O).2] using h.2)
    · exact False.elim ((not_lt_of_ge os) h.1)
  · rcases h with h | h
    · exact Or.inr (by simpa only [(ownV L).1] using h.2)
    · exact False.elim ((not_lt_of_ge ls) h.1)

end N12Compact.CornerSingletonPair
