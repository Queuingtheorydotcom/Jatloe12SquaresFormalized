import Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint.Canonical

/-! ORDINARY-MARKER-HALFPOINT Theorem 1, including the original d=.086
foreign wall marker and the earlier d=0 wall-origin special case.
Both physical orientation signs are proved, not passed as premises.
This source has not been compiled. -/
namespace N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint
open S12 S12Pilot
set_option Elab.async false

theorem point (q : OpenSquare) (d : ℝ) (h : Input q d) : q.Inside 1 (-1/2) := by
  obtain ⟨r,cp,range,side,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side same
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact positive r d data cp sign
      (by simpa only [abs_of_nonneg sign] using range)
  · exact negative r d (-r.s) data (by ring) cp (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

theorem point_original (q : OpenSquare) (d : ℝ) (side : 1<q.side)
    (dn : 0≤d) (du : d≤13/50)
    (marker : q.Inside (47/20) (33/20))
    (near : q.Inside 3 (87/50)) (far : q.Inside 3 (8/5))
    (missingInward : ¬q.Inside (113/50) 2)
    (missingRight : ¬q.Inside (3+d) 2)
    (missingCorner : ¬q.Inside 3 1)
    (missingLower : ¬q.Inside (113/50) 1) : q.Inside 3 (3/2) := by
  let data : Input (q.translated 2 2) d := {
    side := side
    offsetNonnegative := dn
    offsetUpper := du
    marker := by norm_num [inside_translated_iff]; exact marker
    near := by norm_num [inside_translated_iff]; exact near
    far := by norm_num [inside_translated_iff]; exact far
    missingInward := by norm_num [inside_translated_iff]; exact missingInward
    missingRight := by
      intro own
      apply missingRight
      have actual := (inside_translated_iff _ _ _ _ _).mp own
      convert actual using 1 <;> ring
    missingCorner := by norm_num [inside_translated_iff]; exact missingCorner
    missingLower := by norm_num [inside_translated_iff]; exact missingLower
  }
  have result := point (q.translated 2 2) d data
  norm_num [inside_translated_iff] at result
  exact result

/-- The actual northeast application from the C1089 final-sector
reduction. The foreign right marker suffices before any right-origin
conclusion is used. Each omitted auxiliary remains a separate input. -/
theorem northeast_halfpoint (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (near : q.Inside 3 (113/50)) (far : q.Inside 3 (12/5))
    (missingInward : ¬q.Inside (113/50) 2)
    (missingRight : ¬q.Inside (1543/500) 2)
    (missingCorner : ¬q.Inside 3 3)
    (missingLower : ¬q.Inside (113/50) 3) : q.Inside 3 (5/2) := by
  have result := point_original (pullY q) (43/500) side (by norm_num) (by norm_num)
    (by norm_num [inside_pullY]; exact marker)
    (by norm_num [inside_pullY]; exact near)
    (by norm_num [inside_pullY]; exact far)
    (by norm_num [inside_pullY]; exact missingInward)
    (by norm_num [inside_pullY]; exact missingRight)
    (by norm_num [inside_pullY]; exact missingCorner)
    (by norm_num [inside_pullY]; exact missingLower)
  norm_num [inside_pullY] at result
  exact result

/-- The ordinary northwest application uses the original left marker
and the genuine paired northwest corner as two separate omissions. -/
theorem northwest_halfpoint (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (33/20) (47/20))
    (near : q.Inside 1 (113/50)) (far : q.Inside 1 (12/5))
    (missingInward : ¬q.Inside (87/50) 2)
    (missingRight : ¬q.Inside (457/500) 2)
    (missingCorner : ¬q.Inside 1 3)
    (missingLower : ¬q.Inside (87/50) 3) : q.Inside 1 (5/2) := by
  have result := point_original (pullY (pullX q)) (43/500) side (by norm_num) (by norm_num)
    (by norm_num [inside_pullY,inside_pullX]; exact marker)
    (by norm_num [inside_pullY,inside_pullX]; exact near)
    (by norm_num [inside_pullY,inside_pullX]; exact far)
    (by norm_num [inside_pullY,inside_pullX]; exact missingInward)
    (by norm_num [inside_pullY,inside_pullX]; exact missingRight)
    (by norm_num [inside_pullY,inside_pullX]; exact missingCorner)
    (by norm_num [inside_pullY,inside_pullX]; exact missingLower)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

#print axioms point
#print axioms northeast_halfpoint
#print axioms northwest_halfpoint
end N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint
