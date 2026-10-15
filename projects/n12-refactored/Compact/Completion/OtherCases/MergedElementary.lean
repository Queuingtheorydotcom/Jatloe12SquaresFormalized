import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! Elementary actual merged-western point comparisons. Both original
western markers remain owned; the two eastern markers are true exclusions. -/
namespace N12Compact.Completion.OtherCases.MergedElementary
open S12 S12Pilot
set_option Elab.async false

theorem horizontal (q : OpenSquare) (side : 1<q.side)
    (south : q.Inside (-7/20) (-7/20)) (north : q.Inside (-7/20) (7/20))
    (inner : q.Inside (-13/50) 0)
    (missingSE : ¬q.Inside (7/20) (-7/20))
    (missingNE : ¬q.Inside (7/20) (7/20)) : q.Inside (-1/2) 0 := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have p := (same _ _).mpr south
  have n := (same _ _).mpr north
  have d := (same _ _).mpr inner
  have bounds := abs_le.mp range
  apply (same _ _).mp
  by_contra missing
  have xHighU : r.c*(-1/2)<r.loU+r.side := by linarith only [d.2.1,cp]
  have xLowV : r.loV< -r.s*(-1/2) := by linarith only [p.2.2.1,cp,bounds.1]
  have xHighV : -r.s*(-1/2)<r.loV+r.side := by linarith only [n.2.2.2,cp,bounds.2]
  have xLowerU : r.c*(-1/2)≤r.loU := by
    apply le_of_not_gt
    intro low
    apply missing
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
      And.intro low (And.intro xHighU (And.intro xLowV xHighV))
  by_cases sign : 0≤r.s
  · have lowU : r.loU<r.c*(7/20)+r.s*(7/20) := by linarith only [d.1,cp,sign]
    have lowV : r.loV< -r.s*(7/20)+r.c*(7/20) := by linarith only [p.2.2.1,bounds.2]
    have highV : -r.s*(7/20)+r.c*(7/20)<r.loV+r.side := by linarith only [n.2.2.2,sign]
    have short := (short_projections r (17/20) (7/20) (by norm_num)).2.1
    have highU : r.c*(7/20)+r.s*(7/20)<r.loU+r.side := by
      linarith only [xLowerU,side',short]
    exact missingNE ((same _ _).mp ⟨lowU,highU,lowV,highV⟩)
  · have negative : r.s≤0 := le_of_not_ge sign
    have lowU : r.loU<r.c*(7/20)+r.s*(-7/20) := by linarith only [d.1,cp,negative]
    have lowV : r.loV< -r.s*(7/20)+r.c*(-7/20) := by linarith only [p.2.2.1,negative]
    have highV : -r.s*(7/20)+r.c*(-7/20)<r.loV+r.side := by
      linarith only [n.2.2.2,bounds.1]
    have short := (short_projections r (17/20) (-7/20) (by norm_num)).2.1
    have highU : r.c*(7/20)+r.s*(-7/20)<r.loU+r.side := by
      linarith only [xLowerU,side',short]
    exact missingSE ((same _ _).mp ⟨lowU,highU,lowV,highV⟩)

theorem two_inward_center (q : OpenSquare)
    (south : q.Inside (-7/20) (-7/20)) (north : q.Inside (-7/20) (7/20))
    (inner : q.Inside (-13/50) 0)
    (lower : q.Inside 0 (-13/50)) (upper : q.Inside 0 (13/50)) : q.Inside 0 0 := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have p := (same _ _).mpr south
  have n := (same _ _).mpr north
  have d := (same _ _).mpr inner
  have f := (same _ _).mpr lower
  have g := (same _ _).mpr upper
  apply (same _ _).mp
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero]
  by_cases sign : 0≤r.s
  · refine ⟨?_,?_,?_,?_⟩
    · linarith only [p.1,cp,sign]
    · linarith only [g.2.1,sign]
    · linarith only [f.2.2.1,cp]
    · linarith only [n.2.2.2,cp,sign]
  · have negative : r.s≤0 := le_of_not_ge sign
    have order := (abs_le.mp range).1
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [d.1,cp]
    · linarith only [f.2.1,negative]
    · linarith only [p.2.2.1,cp,negative]
    · linarith only [n.2.2.2,order]

theorem horizontal_original (q : OpenSquare) (side : 1<q.side)
    (south : q.Inside (33/20) (33/20)) (north : q.Inside (33/20) (47/20))
    (inner : q.Inside (87/50) 2)
    (missingSE : ¬q.Inside (47/20) (33/20))
    (missingNE : ¬q.Inside (47/20) (47/20)) : q.Inside (3/2) 2 := by
  have point := horizontal (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact south)
    (by norm_num [inside_translated_iff]; exact north)
    (by norm_num [inside_translated_iff]; exact inner)
    (by norm_num [inside_translated_iff]; exact missingSE)
    (by norm_num [inside_translated_iff]; exact missingNE)
  norm_num [inside_translated_iff] at point
  exact point

theorem two_inward_center_original (q : OpenSquare)
    (south : q.Inside (33/20) (33/20)) (north : q.Inside (33/20) (47/20))
    (inner : q.Inside (87/50) 2)
    (lower : q.Inside 2 (87/50)) (upper : q.Inside 2 (113/50)) : q.Inside 2 2 := by
  have point := two_inward_center (q.translated 2 2)
    (by norm_num [inside_translated_iff]; exact south)
    (by norm_num [inside_translated_iff]; exact north)
    (by norm_num [inside_translated_iff]; exact inner)
    (by norm_num [inside_translated_iff]; exact lower)
    (by norm_num [inside_translated_iff]; exact upper)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms horizontal_original
#print axioms two_inward_center_original
end N12Compact.Completion.OtherCases.MergedElementary

