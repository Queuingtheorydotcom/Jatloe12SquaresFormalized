import Compact.Completion.FiniteCases.C972SoutheastPositive

/-! A center-owning SW square cannot coexist with C972's positive
SE residual.  The full actual SW/SE support comparison covers every
canonical sign of SW.  The center is an explicit branch to be excluded,
not an entrance assumption for the family. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot ABTransverse
open N12Compact.Completion.OtherCases.C983
set_option Elab.async false

theorem positive_southeast_center_impossible (A E : OpenSquare)
    (ac : 0<A.c) (canonical : |A.s|≤A.c)
    (orderE : E.s≤E.c) (same : A.side=E.side)
    (west : A.Inside (-1/2) 0) (south : A.Inside 0 (-1/2))
    (nearA : A.Inside 0 (-13/50)) (center : A.Inside 0 0)
    (markerE : E.Inside (7/20) (-7/20))
    (outerE : E.Inside 1 (-13/50)) (innerE : E.Inside (13/50) 0)
    (data : F4SoutheastSignSupports.Data E)
    (apart : ∀ x y,¬(A.Inside x y ∧ E.Inside x y)) : False := by
  have ec : 0<E.c := by linarith only [data.cosine]
  rcases positive_southeast_alternatives A E ac canonical ec data.sine.le orderE same
      west south nearA markerE outerE innerE apart with first | second | third
  · by_cases sign : 0≤A.s
    · have low := F4SoutheastSignSupports.positive_u E data A.c A.s ac sign
      have own := center.2.1
      linarith only [first,low,own]
    · have low := F4SoutheastSignSupports.negative_w E data A.c (-A.s) ac
        (by linarith only [sign]) (by linarith only [(abs_le.mp canonical).1])
      simp only [neg_neg] at low
      have own := nearA.2.1
      linarith only [first,low,own]
  · have own := (strict_bounds A 0 0 E.c E.s E.unit_normal center).2
    linarith only [second,own,data.lowerU,data.cosineUpper]
  · have negative : 0< -A.s := by linarith only [third.1,ac]
    have low := F4SoutheastSignSupports.positive_u E data (-A.s) A.c negative ac.le
    have own := center.2.2.2
    linarith only [third.2,low,own]

end N12Compact.FiniteCases.C972Local

namespace N12Compact.FiniteCases.C972
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

/-- Actual SW center exclusion in the sole missing-halfpoint residual.
The SE frame, strict positive sign and complete support profile are all
derived before entering the two-square theorem. -/
theorem southwest_center_missing (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2)) :
    ¬(owners p 5).Inside 2 2 := by
  intro center
  obtain ⟨A,ac,canonicalA,shapeA,insideA,_⟩ :=
    ClosedFrames.canonical_frame ((owners p 5).translated 2 2)
  have actualA (x y : ℝ) : A.Inside x y↔(owners p 5).Inside (2+x) (2+y) :=
    (insideA x y).trans (inside_translated_iff _ _ _ _ _)
  obtain ⟨E,shapeE,actualE,en,positive⟩ := exists_positive_southeast p hf missing
  have ec : 0<E.c := by linarith only [(normal_bounds en).1]
  have canonicalE : |E.s|≤E.c := by simpa only [abs_of_pos positive] using en.2.1
  have data := southeast_support_profile p hf missing E shapeE actualE ec canonicalE
  apply C972Local.positive_southeast_center_impossible A E ac canonicalA en.2.1
    (shapeA.trans ((same p 5 6).trans shapeE.symm))
  · apply (actualA _ _).mpr; norm_num; exact southwest_west p hf
  · apply (actualA _ _).mpr; norm_num; exact southwest_south p hf
  · apply (actualA _ _).mpr; norm_num; exact (fixed p hf).southwestF4
  · apply (actualA _ _).mpr; norm_num; exact center
  · apply (actualE _ _).mpr; norm_num; exact (fixed p hf).southeastMarker
  · apply (actualE _ _).mpr; norm_num; exact (fixed p hf).southeastF8
  · apply (actualE _ _).mpr; norm_num; exact southeast_g6_of_missing_halfpoint p hf missing
  · exact data
  · intro x y both
    exact apart p hf 5 6 (by decide) _ _
      ⟨(actualA _ _).mp both.1,(actualE _ _).mp both.2⟩

end
#print axioms southwest_center_missing
end N12Compact.FiniteCases.C972
