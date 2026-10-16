import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Positive
import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Negative
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! The full all-angle ordinary-square/foreign-bar theorem. The actual
C1089 application retains the original singleton bar, the globally absent
marker and the actual left wall-marker owner as separate sources.
Source translation only; no compiler acceptance is asserted. -/
namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
open S12 S12Pilot
set_option Elab.async false

theorem point (q : OpenSquare) (h : Input q) : q.Inside (1/2) 0 := by
  obtain ⟨r,cp,range,side,same,_⟩ := ClosedFrames.canonical_frame q
  have data := h.reframe side same
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact positive r data cp sign (by simpa only [abs_of_nonneg sign] using range)
  · exact negative r data (-r.s) (by ring) cp (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)

theorem point_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (33/20))
    (near : q.Inside 3 (87/50)) (far : q.Inside 3 (8/5))
    (missingRight : ¬q.Inside (1543/500) 2)
    (missingLower : ¬q.Inside (1543/500) 1)
    (segment : ∀ x : ℝ,113/50≤x → x≤72/25 → ¬q.Inside x 1) :
    q.Inside (5/2) 2 := by
  let data : Input (q.translated 2 2) := {
    side := side
    marker := by norm_num [inside_translated_iff]; exact marker
    near := by norm_num [inside_translated_iff]; exact near
    far := by norm_num [inside_translated_iff]; exact far
    missingRight := by norm_num [inside_translated_iff]; exact missingRight
    missingLower := by norm_num [inside_translated_iff]; exact missingLower
    segment := by
      intro x low high own
      have actual : q.Inside (2+x) 1 := by
        simpa only [inside_translated_iff,show (2:ℝ)+(-1)=1 by norm_num] using own
      exact segment (2+x) (by linarith only [low]) (by linarith only [high]) actual
  }
  have result := point (q.translated 2 2) data
  norm_num [inside_translated_iff] at result
  exact result

/-- Section 4's actual reflected application. The bar is entirely in K;
the isolated lower-marker exclusion does not assert any owner for it.
The left owner's strict marker and a hypothetical extra point would span
the newly forced crosspoint, so that owner must omit the extra point. -/
theorem southwest_point_and_left_omission (A K L : OpenSquare)
    (side : 1<A.side)
    (marker : A.Inside (33/20) (33/20))
    (near : A.Inside 1 (87/50)) (far : A.Inside 1 (8/5))
    (barNear : K.Inside (28/25) 1) (barFar : K.Inside (87/50) 1)
    (leftMarker : L.Inside (457/500) 2)
    (absentMarker : ¬A.Inside (457/500) 1)
    (apartBar : ∀ x y,¬(A.Inside x y ∧ K.Inside x y))
    (apartLeft : ∀ x y,¬(A.Inside x y ∧ L.Inside x y)) :
    A.Inside (3/2) 2 ∧ ¬L.Inside (87/50) 2 := by
  let r := (pullX A).translated 2 2
  have chart (x y : ℝ) : r.Inside x y ↔ A.Inside (2-x) (2+y) := by
    dsimp only [r]
    rw [inside_translated_iff,inside_pullX,show (4:ℝ)-(2+x)=2-x by ring]
  have bar := WallProfile.vertical_owned (pullSwap K) 1 (28/25) (87/50)
    (by norm_num)
    (by norm_num [inside_pullSwap]; exact barNear)
    (by norm_num [inside_pullSwap]; exact barFar)
  let data : Input r := {
    side := side
    marker := (chart _ _).mpr (by convert marker using 1 <;> norm_num)
    near := (chart _ _).mpr (by convert near using 1 <;> norm_num)
    far := (chart _ _).mpr (by convert far using 1 <;> norm_num)
    missingRight := by
      intro own
      have actual := (chart _ _).mp own
      norm_num at actual
      exact apartLeft _ _ ⟨actual,leftMarker⟩
    missingLower := by
      intro own
      apply absentMarker
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num
    segment := by
      intro x low high own
      have actual := (chart _ _).mp own
      norm_num only at actual
      have foreign := (inside_pullSwap _ _ _).mp
        (bar (2-x) (by linarith only [high]) (by linarith only [low]))
      exact apartBar _ _ ⟨actual,foreign⟩
  }
  have crosspoint : A.Inside (3/2) 2 := by
    have result := (chart _ _).mp (point r data)
    convert result using 1 <;> norm_num
  refine ⟨crosspoint,?_⟩
  intro extra
  have duplicate : L.Inside (3/2) 2 := by
    convert inside_segment L (457/500) 2 (87/50) 2 (293/413)
      leftMarker extra (by norm_num) (by norm_num) using 1 <;> norm_num
  exact apartLeft _ _ ⟨crosspoint,duplicate⟩

#print axioms point
#print axioms southwest_point_and_left_omission
end N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
