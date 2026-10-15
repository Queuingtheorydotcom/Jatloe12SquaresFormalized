import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The top-only outward extension, C974-C976-CENTRAL-CROSSPOINTS
Section3. The omitted half-unit point may have its own actual source. -/
namespace N12Compact.Completion.OtherCases.TopOnlyExtension
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1) :
    q.Inside (1/2) 1 := by
  by_contra missing
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have hLowU : q.loU<q.c*(1/2)+q.s := by linarith only [anchor.1,cp]
  have hLowV : q.loV< -q.s*(1/2)+q.c := by linarith only [marker.2.2.1,cp,order]
  have hHighV : -q.s*(1/2)+q.c<q.loV+q.side := by linarith only [anchor.2.2.2,sn]
  have hUpperU : q.loU+q.side≤q.c*(1/2)+q.s := by
    apply le_of_not_gt
    intro high
    apply missing
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro hLowU (And.intro high (And.intro hLowV hHighV))
  have pLowU : q.loU<q.s := by linarith only [hUpperU,side,cu]
  have pHighU : q.s<q.loU+q.side := by linarith only [anchor.2.1,cp]
  have pLowV : q.loV<q.c := by linarith only [marker.2.2.1,cp,sn]
  have pUpperV : q.loV+q.side≤q.c := by
    apply le_of_not_gt
    intro high
    apply missingP
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro pLowU (And.intro pHighU (And.intro pLowV high))
  have lHighU : q.s*(13/50)<q.loU+q.side := by linarith only [marker.2.1,cp,sn]
  have lHighV : q.c*(13/50)<q.loV+q.side := by linarith only [anchor.2.2.2,cp,order]
  have lLowV : q.loV<q.c*(13/50) := by linarith only [pUpperV,side,cu]
  have lLowerU : q.s*(13/50)≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingL
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro low (And.intro lHighU (And.intro lLowV lHighV))
  have short := (short_projections q (1/2) (37/50) (by norm_num)).2.1
  linarith only [lLowerU,hUpperU,side,short]

private theorem negative (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingX : ¬q.Inside (1/2) 0) : q.Inside (1/2) 1 := by
  by_contra missing
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have hLowU : q.loU<q.c*(1/2)+q.s := by linarith only [anchor.1,cp]
  have hLowV : q.loV< -q.s*(1/2)+q.c := by linarith only [anchor.2.2.1,sn]
  have pHighU : q.s<q.loU+q.side := by linarith only [anchor.2.1,cp]
  have pLowV : q.loV<q.c := by linarith only [marker.2.2.1,cp,order]
  have pHighV : q.c<q.loV+q.side := by linarith only [anchor.2.2.2,sn]
  have pLowerU : q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingP
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_one] using
      And.intro low (And.intro pHighU (And.intro pLowV pHighV))
  have hHighU : q.c*(1/2)+q.s<q.loU+q.side := by linarith only [pLowerU,side,cu]
  have hUpperV : q.loV+q.side≤ -q.s*(1/2)+q.c := by
    apply le_of_not_gt
    intro high
    apply missing
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro hLowU (And.intro hHighU (And.intro hLowV high))
  have xLowU : q.loU<q.c*(1/2) := by linarith only [marker.1,cp,sn]
  have xLowV : q.loV< -q.s*(1/2) := by linarith only [hUpperV,side,cu]
  have xHighV : -q.s*(1/2)<q.loV+q.side := by linarith only [marker.2.2.2,cp,order]
  have xUpperU : q.loU+q.side≤q.c*(1/2) := by
    apply le_of_not_gt
    intro high
    apply missingX
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
      And.intro xLowU (And.intro high (And.intro xLowV xHighV))
  have lHighU : q.s*(13/50)<q.loU+q.side := by linarith only [marker.2.1,cp,order]
  have lHighV : q.c*(13/50)<q.loV+q.side := by linarith only [anchor.2.2.2,cp,sn]
  have shortL := (short_projections q (1/2) (-13/50) (by norm_num)).2.1
  have lLowU : q.loU<q.s*(13/50) := by linarith only [xUpperU,side,shortL]
  have lLowerV : q.c*(13/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingL
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro lLowU (And.intro lHighU (And.intro low lHighV))
  have short := (short_projections q (1/2) (37/50) (by norm_num)).2.2.2
  linarith only [lLowerV,hUpperV,side,short]

theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (anchor : q.Inside (2/5) 1)
    (missingL : ¬q.Inside 0 (13/50)) (missingP : ¬q.Inside 0 1)
    (missingX : ¬q.Inside (1/2) 0) : q.Inside (1/2) 1 := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr anchor
  have l : ¬r.Inside 0 (13/50) := fun h => missingL ((same _ _).mp h)
  have p : ¬r.Inside 0 1 := fun h => missingP ((same _ _).mp h)
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range) m a l p)
  · exact (same _ _).mp (negative r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m a l p
      (fun h => missingX ((same _ _).mp h)))

theorem point_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20)) (anchor : q.Inside (12/5) 3)
    (missingL : ¬q.Inside 2 (113/50)) (missingP : ¬q.Inside 2 3)
    (missingX : ¬q.Inside (5/2) 2) : q.Inside (5/2) 3 := by
  have point := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact anchor)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingX)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms point_original
end N12Compact.Completion.OtherCases.TopOnlyExtension

