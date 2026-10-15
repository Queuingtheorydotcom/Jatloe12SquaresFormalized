import Compact.Completion.C1092.MPPMMissingNegativeActual
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointScalars

/-! The genuine negative missing-successor profile in the common
physical chart of STEEP-POSITIVE-MISSING-NEGATIVE-CROSSPOINT. Its four
faces and large angle are produced by one simultaneous inverse-quarter
turn of the full raw marker/halfpoint/foreign-bar profile. Source only. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
open S12 S12Pilot C977CornerCubic C1092MPPMMissingNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

structure RecipientInput (E B : OpenSquare) : Prop where
  side : 1<E.side
  normal : Normal E.c (-E.s)
  marker : E.Inside (7/20) (-7/20)
  ordinaryP : E.Inside (13/50) (-1)
  ordinaryG : E.Inside (2/5) (-1)
  halfpoint : E.Inside (1/2) (-1)
  corner : ¬E.Inside 1 (-1)
  forward : ¬E.Inside 0 (-13/50)
  bar : ∀ y,-(14/25)≤y→y≤-(13/50)→¬E.Inside 1 y
  originB : B.Inside 0 (-1)
  apart : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)

structure RecipientFaces (E : OpenSquare) : Prop where
  lowerU : -(13/50)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -E.c≤E.loV
  upperV : E.loV+E.side≤-E.s-(14/25)*E.c
  negative : E.s<0
  large : 252/373≤-E.s

/-- No lower/upper face or steep angle is assumed for the missing
negative successor. The entire right bar is transported together. -/
theorem recipient_faces (E B : OpenSquare) (h : RecipientInput E B) : RecipientFaces E := by
  let D := C1092MMMPEndingAxes.clockwise
    (C1092MMMPEndingAxes.clockwise (C1092MMMPEndingAxes.clockwise E))
  have actual (x y : ℝ) : D.Inside x y↔E.Inside (-y) x := by
    simp only [D,C1092MMMPEndingAxes.inside_clockwise,neg_neg]
  have core : C1092MPPMMissingNegativeProfile.Core D := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · apply (actual _ _).mpr; norm_num; exact h.marker
    · apply (actual _ _).mpr; norm_num; exact h.ordinaryP
    · apply (actual _ _).mpr; norm_num; exact h.ordinaryG
    · apply (actual _ _).mpr; norm_num; exact h.halfpoint
    · intro own
      have original := (actual _ _).mp own
      norm_num at original
      exact h.corner original
    · intro own
      have original := (actual _ _).mp own
      norm_num at original
      exact h.forward original
    · intro y low high own
      have original := (actual _ _).mp own
      norm_num at original
      exact h.bar y low high original
  have previous : ¬D.Inside (-1) 0 := by
    intro own
    have original := (actual _ _).mp own
    norm_num at original
    exact h.apart 0 (-1) ⟨h.originB,original⟩
  have strong := C1092MPPMMissingNegativeProfile.strong_profile D h.side h.normal core previous
  have large := C1092MPPMMissingNegativeProfile.StrongFaces.sine_lower D h.side h.normal strong
  have low := strong.lowerU
  have high := strong.upperU
  have first := strong.lowerV
  have last := strong.upperV
  have u : D.loU=E.loV := by dsimp [D,C1092MMMPEndingAxes.clockwise]; ring
  have v : D.loV= -E.loU-E.side := rfl
  rw [u] at low high
  rw [v] at first last
  change -E.c≤E.loV at low
  change E.loV+E.side≤-E.s-(14/25)*E.c at high
  change E.s-E.c≤-E.loU-E.side at first
  change -E.loU-E.side+E.side≤(13/50)*E.s at last
  refine ⟨?_,?_,low,high,strong.negative,large⟩ <;> linarith only [first,last]

end
#print axioms recipient_faces
end N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
