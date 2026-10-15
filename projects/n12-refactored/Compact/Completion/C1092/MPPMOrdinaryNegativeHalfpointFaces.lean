import Compact.Completion.C1092.MPPMOrdinaryNegativeHalfpointScalars
import Compact.Completion.C1092.WholeSupports

/-! The literal face and actual separating-axis steps of
`C1092-MPPM-ORDINARY-NEGATIVE-HALFPOINT.md`, sections 2 and 6.
No additional wall or side upper bound occurs. Source-only translation. -/
namespace N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem negative_frame (Q : OpenSquare) (cp : 0<Q.c)
    (sn : Q.s≤0) (order : -Q.s≤Q.c) : Frame Q.c (-Q.s) :=
  ⟨cp,by linarith only [sn],order,by nlinarith only [Q.unit_normal]⟩

/-- A missing outer halfpoint can only lie beyond the upper longitudinal
face; the other three strict bands are supplied by the actual anchors. -/
theorem missing_face (E : OpenSquare) (frame : Frame E.c (-E.s))
    (marker : E.Inside (7/20) (-7/20))
    (bar : E.Inside (2/5) (-1)) (missing : ¬E.Inside (1/2) (-1)) :
    E.loU+E.side≤E.c/2-E.s := by
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [high,bar.1,bar.2.2.1,marker.2.2.2,
      frame.positive,frame.nonnegative,frame.ordered]

/-- All eight oriented actual square face axes are considered. Strict
marker ownership and the target's first bar endpoint leave just the two
forward longitudinal supports. -/
theorem axes (C E : OpenSquare) (same : C.side=E.side)
    (cf : Frame C.c (-C.s)) (ef : Frame E.c (-E.s))
    (source : C.Inside (-7/20) (-7/20))
    (target : E.Inside (7/20) (-7/20))
    (bar : E.Inside (13/50) (-1))
    (apart : ∀ x y, ¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
  have choices := CongruentSAT.faceSeparation_of_disjoint C E same apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at choices
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius C nx ny+supportRadius E nx ny=R)
      (sep : R≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [identity])
  rcases choices with cu | cv | eu | ev
  · have sep := separateAxis C.c C.s _ (parallel_radius C E) cu
    have a := strict_bounds C _ _ C.c C.s C.unit_normal source
    have b := strict_bounds E _ _ C.c C.s C.unit_normal target
    rcases sep with forward | reverse
    · left
      simpa only [(ownU C).2] using forward
    · exfalso
      linarith only [reverse,a.1,b.2,cf.positive]
  · have sep := separateAxis (-C.s) C.c _ (transverse_radius C E) cv
    have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    have a := strict_bounds C _ _ (-C.s) C.c unit source
    have b := strict_bounds E _ _ (-C.s) C.c unit target
    have p := strict_bounds E _ _ (-C.s) C.c unit bar
    rcases sep with forward | reverse
    · exfalso
      linarith only [forward,a.2,p.1,cf.positive,cf.ordered]
    · exfalso
      linarith only [reverse,a.1,b.2,cf.nonnegative]
  · have identity : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]
      exact parallel_radius E C
    have sep := separateAxis E.c E.s _ identity eu
    have a := strict_bounds C _ _ E.c E.s E.unit_normal source
    have b := strict_bounds E _ _ E.c E.s E.unit_normal target
    rcases sep with forward | reverse
    · right
      simpa only [(ownU E).1] using forward
    · exfalso
      linarith only [reverse,a.1,b.2,ef.positive]
  · have identity : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]
      exact transverse_radius E C
    have sep := separateAxis (-E.s) E.c _ identity ev
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    have a := strict_bounds C _ _ (-E.s) E.c unit source
    have b := strict_bounds E _ _ (-E.s) E.c unit target
    have p := strict_bounds E _ _ (-E.s) E.c unit bar
    rcases sep with forward | reverse
    · exfalso
      linarith only [forward,a.2,p.1,ef.positive,ef.ordered]
    · exfalso
      linarith only [reverse,a.1,b.2,ef.nonnegative]

/-- Section 6's forward-owned predecessor: both caps follow from literal
ownership and exclusion of the actual left and northwest markers.
The missing-forward alternative is a separate geometric obligation. -/
theorem forward_owned_caps (C : OpenSquare) (frame : Frame C.c (-C.s))
    (ordinary : C.Inside (-1) (-13/50))
    (bar : C.Inside (-1) (-2/5))
    (forward : C.Inside (-13/50) 0)
    (leftMarker : ¬C.Inside (-543/500) 0)
    (northMarker : ¬C.Inside (-7/20) (7/20)) :
    -(543/500)*C.c≤C.loU ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  constructor
  · apply le_of_not_gt
    intro low
    apply leftMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,ordinary.2.1,bar.2.2.1,forward.2.2.2,
        frame.positive,frame.nonnegative,frame.ordered]
  · apply le_of_not_gt
    intro high
    apply northMarker
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,ordinary.1,forward.2.1,forward.2.2.1,
        frame.positive,frame.nonnegative,frame.ordered]

end N12Compact.C1092MPPMOrdinaryNegativeHalfpoint
