import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The inward square with an actual top anchor reaches the sharp common
point. This is a strengthened target in the same exact face argument of
C974-C976-DUPLICATE-POINT Theorem2; all original hypotheses are retained. -/
namespace N12Compact.Completion.OtherCases.InwardTopPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingB : ¬q.Inside (7/20) (-7/20)) :
    q.Inside (21/40) (1/8) := by
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have yLowU : q.loU < q.c*(21/40)+q.s*(1/8) := by
    linarith only [elbow.1,cp,sn]
  have yHighV : -q.s*(21/40)+q.c*(1/8) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  by_cases steep : q.c/6 ≤ q.s
  · have fLowU : q.loU < q.c*(13/50)+q.s := by
      linarith only [marker.1,steep,cp]
    have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
      linarith only [top.2.1,cp]
    have fLowV : q.loV < -q.s*(13/50)+q.c := by
      linarith only [marker.2.2.1,cp,sn]
    have fUpperV : q.loV+q.side ≤ -q.s*(13/50)+q.c := by
      apply le_of_not_gt
      intro high
      apply missingF
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro fLowU (And.intro fHighU (And.intro fLowV high))
    have short := (short_projections q (-53/200) (7/8) (by norm_num)).2.2.2
    have yLowV : q.loV < -q.s*(21/40)+q.c*(1/8) := by
      linarith only [fUpperV,side,short]
    have yHighU : q.c*(21/40)+q.s*(1/8) < q.loU+q.side := by
      linarith only [top.2.1,cp,steep]
    exact ⟨yLowU,yHighU,yLowV,yHighV⟩
  · have shallow : q.s < q.c/6 := lt_of_not_ge steep
    have yLowV : q.loV < -q.s*(21/40)+q.c*(1/8) := by
      linarith only [elbow.2.2.1,cp,shallow]
    have bLowU : q.loU < q.c*(7/20)+q.s*(-7/20) := by
      linarith only [elbow.1,cp,shallow]
    have bHighU : q.c*(7/20)+q.s*(-7/20) < q.loU+q.side := by
      linarith only [marker.2.1,sn]
    have bHighV : -q.s*(7/20)+q.c*(-7/20) < q.loV+q.side := by
      linarith only [elbow.2.2.2,cp,sn]
    have bLowerV : -q.s*(7/20)+q.c*(-7/20) ≤ q.loV :=
      le_of_not_gt (fun h => missingB ⟨bLowU,bHighU,h,bHighV⟩)
    have lHighU : q.c*(-7/20)+q.s*(7/20) < q.loU+q.side := by
      linarith only [inward.2.1,cp,shallow]
    have lLowV : q.loV < -q.s*(-7/20)+q.c*(7/20) := by
      linarith only [inward.2.2.1,cp,sn]
    have lHighV : -q.s*(-7/20)+q.c*(7/20) < q.loV+q.side := by
      linarith only [bLowerV,side,cu,shallow]
    have lLowerU : q.c*(-7/20)+q.s*(7/20) ≤ q.loU :=
      le_of_not_gt (fun h => missingL ⟨h,lHighU,lLowV,lHighV⟩)
    have yHighU : q.c*(21/40)+q.s*(1/8) < q.loU+q.side := by
      linarith only [lLowerU,side,cu,sn]
    exact ⟨yLowU,yHighU,yLowV,yHighV⟩

private theorem negative_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : q.s ≤ 0) (order : -q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1) :
    q.Inside (21/40) (1/8) := by
  have yLowU : q.loU < q.c*(21/40)+q.s*(1/8) := by
    linarith only [elbow.1,cp,order]
  have yLowV : q.loV < -q.s*(21/40)+q.c*(1/8) := by
    linarith only [elbow.2.2.1,cp,sn]
  have yHighV : -q.s*(21/40)+q.c*(1/8) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
    linarith only [top.2.1,cp]
  have fHighV : -q.s*(13/50)+q.c < q.loV+q.side := by
    linarith only [top.2.2.2,sn]
  have fLowV : q.loV < -q.s*(13/50)+q.c := by
    linarith only [inward.2.2.1,cp,sn]
  have fLowerU : q.c*(13/50)+q.s ≤ q.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro low (And.intro fHighU (And.intro fLowV fHighV))
  have short := (short_projections q (53/200) (-7/8) (by norm_num)).2.1
  have yHighU : q.c*(21/40)+q.s*(1/8) < q.loU+q.side := by
    linarith only [fLowerU,side,short]
  exact ⟨yLowU,yHighU,yLowV,yHighV⟩

theorem point (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingB : ¬q.Inside (7/20) (-7/20)) :
    q.Inside (21/40) (1/8) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr inward
  have d := (same _ _).mpr elbow
  have t := (same _ _).mpr top
  have f : ¬r.Inside (13/50) 1 := fun h => missingF ((same _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive_point r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range) m a d t f
      (fun h => missingL ((same _ _).mp h)) (fun h => missingB ((same _ _).mp h)))
  · exact (same _ _).mp (negative_point r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m a d t f)

theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20)) (inward : q.Inside 2 (113/50))
    (elbow : q.Inside (113/50) 2) (top : q.Inside (12/5) 3)
    (missingF : ¬q.Inside (113/50) 3)
    (missingL : ¬q.Inside (33/20) (47/20))
    (missingB : ¬q.Inside (47/20) (33/20)) :
    q.Inside (101/40) (17/8) := by
  have point := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact inward)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact top)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingB)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms point_original
end N12Compact.Completion.OtherCases.InwardTopPoint

