import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! Theorem A of MERGED-RIGHT-PATTERN-4: three owned anchors and four
genuine singleton point exclusions force the strict near-center point.
Only three exact unit-normal projection bounds are needed. -/
namespace N12Compact.CommonCases.SouthwestPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s)
    (marker : q.Inside (33/20) (33/20))
    (inward : q.Inside 2 (87/50)) (elbow : q.Inside (87/50) 2)
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (87/50) 1) :
    q.Inside (39/20) (39/20) := by
  have kLowU : q.loU < q.c*(39/20)+q.s*(39/20) := by
    linarith only [marker.1,cp,sn]
  have kLowV : q.loV < -q.s*(39/20)+q.c*(39/20) := by
    linarith only [inward.2.2.1,cp,sn]
  have kHighV : -q.s*(39/20)+q.c*(39/20) < q.loV+q.side := by
    linarith only [elbow.2.2.2,cp,sn]
  have kHighU : q.c*(39/20)+q.s*(39/20) < q.loU+q.side := by
    by_contra bad
    have face : q.loU+q.side ≤ q.c*(39/20)+q.s*(39/20) := le_of_not_gt bad
    have kl := short_projections q (19/20) (3/10) (by norm_num)
    have lb := short_projections q (-37/50) (13/20) (by norm_num)
    have kb := short_projections q (21/100) (19/20) (by norm_num)
    have lLowU : q.loU < q.c*1+q.s*(33/20) := by
      linarith only [face,side,kl.2.1]
    have lHighU : q.c*1+q.s*(33/20) < q.loU+q.side := by
      linarith only [marker.2.1,cp]
    have lLowV : q.loV < -q.s*1+q.c*(33/20) := by
      linarith only [marker.2.2.1,sn]
    have lFace : q.loV+q.side ≤ -q.s*1+q.c*(33/20) :=
      le_of_not_gt (fun h => missingL ⟨lLowU,lHighU,lLowV,h⟩)
    have bHighU : q.c*(87/50)+q.s*1 < q.loU+q.side := by
      linarith only [elbow.2.1,sn]
    have bLowV : q.loV < -q.s*(87/50)+q.c*1 := by
      linarith only [lFace,side,lb.2.2.2]
    have bHighV : -q.s*(87/50)+q.c*1 < q.loV+q.side := by
      linarith only [marker.2.2.2,cp,sn]
    have bFace : q.c*(87/50)+q.s*1 ≤ q.loU :=
      le_of_not_gt (fun h => missingB ⟨h,bHighU,bLowV,bHighV⟩)
    linarith only [face,bFace,side,kb.2.1]
  exact ⟨kLowU,kHighU,kLowV,kHighV⟩

theorem point (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (33/20) (33/20))
    (inward : q.Inside 2 (87/50)) (elbow : q.Inside (87/50) 2)
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (87/50) 1)
    (missingB' : ¬q.Inside (33/20) 1) (missingL' : ¬q.Inside 1 (87/50)) :
    q.Inside (39/20) (39/20) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr inward
  have d := (same _ _).mpr elbow
  have l : ¬r.Inside 1 (33/20) := fun h => missingL ((same _ _).mp h)
  have b : ¬r.Inside (87/50) 1 := fun h => missingB ((same _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive r side' cp sign m a d l b)
  · let swapped := turnFrame (turnFrame (turnFrame (pullSwap r)))
    have h := positive swapped side'
      (by simpa [swapped,turnFrame,pullSwap] using cp)
      (by change 0 ≤ -r.s; linarith only [sign])
      (by simpa [swapped,inside_pullSwap] using m)
      (by simpa [swapped,inside_pullSwap] using d)
      (by simpa [swapped,inside_pullSwap] using a)
      (by
        intro own
        apply missingB'
        exact (same _ _).mp (by simpa [swapped,inside_pullSwap] using own))
      (by
        intro own
        apply missingL'
        exact (same _ _).mp (by simpa [swapped,inside_pullSwap] using own))
    exact (same _ _).mp (by simpa [swapped,inside_pullSwap] using h)

#print axioms point
end N12Compact.CommonCases.SouthwestPoint
