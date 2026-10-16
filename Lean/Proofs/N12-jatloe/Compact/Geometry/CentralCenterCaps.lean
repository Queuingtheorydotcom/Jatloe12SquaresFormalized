import Compact.Geometry.ABTransverse

/-! Genuine central-marker exclusions bound both upper faces of a square
which owns the center. The argument retains both lower-face escapes and
uses a strict width contradiction, uniformly over signed canonical frames. -/
namespace N12Compact.CentralCenterCaps

open S12 S12Pilot

/-- In a nonnegative canonical frame, the northwest marker selects the
upper transverse face. Its cap then removes the southeast lower-face
escape because the available transverse width is less than one. -/
theorem positive_caps (A : OpenSquare)
    (positive : 0<A.c) (sign : 0≤A.s) (canonical : A.s≤A.c)
    (side : 1<A.side) (center : A.Inside 2 2)
    (left : A.Inside (3/2) 2)
    (missingNW : ¬A.Inside (33/20) (47/20))
    (missingSE : ¬A.Inside (47/20) (33/20)) :
    A.loU+A.side≤(47/20)*A.c+(33/20)*A.s ∧
      A.loV+A.side≤(47/20)*A.c-(33/20)*A.s := by
  have upperV : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s := by
    apply le_of_not_gt
    intro high
    apply missingNW
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [left.1,positive,sign]
    · nlinarith only [center.2.1,canonical]
    · nlinarith only [center.2.2.1,positive,sign]
    · linarith only [high]
  have short : (7/10)*(A.c+A.s)<1 := by
    have squared : (A.c+A.s)^2≤2 := by
      nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s)]
    nlinarith only [squared]
  refine ⟨?_,upperV⟩
  apply le_of_not_gt
  intro high
  by_cases lowerV : A.loV<(33/20)*A.c-(47/20)*A.s
  · apply missingSE
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [center.1,canonical]
    · linarith only [high]
    · linarith only [lowerV]
    · nlinarith only [center.2.2.2,positive,sign]
  · have low : (33/20)*A.c-(47/20)*A.s≤A.loV := le_of_not_gt lowerV
    linarith only [upperV,low,short,side]

private noncomputable def swapFrame (A : OpenSquare) : OpenSquare where
  c := A.c
  s := -A.s
  loU := A.loV
  loV := A.loU
  side := A.side
  unit_normal := by nlinarith only [A.unit_normal]
  side_pos := A.side_pos

private theorem inside_swapFrame (A : OpenSquare) (x y : ℝ) :
    (swapFrame A).Inside x y↔A.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

/-- Both upper faces obey the same coordinate formulas for every signed
canonical frame. The negative sector is a physical diagonal reflection
of the preceding argument, using the other genuine crosspoint. -/
theorem signed_caps (A : OpenSquare)
    (positive : 0<A.c) (canonical : |A.s|≤A.c)
    (side : 1<A.side) (center : A.Inside 2 2)
    (left : A.Inside (3/2) 2) (low : A.Inside 2 (3/2))
    (missingNW : ¬A.Inside (33/20) (47/20))
    (missingSE : ¬A.Inside (47/20) (33/20)) :
    A.loU+A.side≤(47/20)*A.c+(33/20)*A.s ∧
      A.loV+A.side≤(47/20)*A.c-(33/20)*A.s := by
  by_cases sign : 0≤A.s
  · exact positive_caps A positive sign (abs_le.mp canonical).2
      side center left missingNW missingSE
  · have reflected := positive_caps (swapFrame A) positive
        (by dsimp [swapFrame]; linarith only [sign])
        (by dsimp [swapFrame]; linarith only [(abs_le.mp canonical).1])
        side ((inside_swapFrame A 2 2).mpr center)
        ((inside_swapFrame A (3/2) 2).mpr low)
        (fun h => missingSE ((inside_swapFrame A (33/20) (47/20)).mp h))
        (fun h => missingNW ((inside_swapFrame A (47/20) (33/20)).mp h))
    dsimp [swapFrame] at reflected
    constructor <;> nlinarith only [reflected.1,reflected.2]

#print axioms positive_caps
#print axioms signed_caps
end N12Compact.CentralCenterCaps
