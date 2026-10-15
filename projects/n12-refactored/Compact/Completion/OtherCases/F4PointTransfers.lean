import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! Both exact F4 point transfers. Only the stated owned and omitted
points are used; all canonical signs and face contacts are included. -/
namespace N12Compact.Completion.OtherCases.F4PointTransfers
open S12 S12Pilot
set_option Elab.async false

private theorem horizontal_positive (q : OpenSquare)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50)) :
    q.Inside (1/2) 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [elbow.1,cp]
  · linarith only [outer.2.1,cp,order]
  · linarith only [marker.2.2.1,cp,order]
  · linarith only [elbow.2.2.2,sn]

private theorem horizontal_negative (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingF : ¬q.Inside 0 (-13/50)) (missingT : ¬q.Inside (1/2) (-1)) :
    q.Inside (1/2) 0 := by
  by_contra missing
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have xLowU : q.loU<q.c*(1/2) := by linarith only [elbow.1,cp]
  have xHighU : q.c*(1/2)<q.loU+q.side := by linarith only [outer.2.1,cp,sn]
  have xLowV : q.loV< -q.s*(1/2) := by linarith only [elbow.2.2.1,sn]
  have xUpperV : q.loV+q.side≤ -q.s*(1/2) := by
    apply le_of_not_gt
    intro high
    apply missing
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
      And.intro xLowU (And.intro xHighU (And.intro xLowV high))
  have fHighU : q.s*(-13/50)<q.loU+q.side := by linarith only [elbow.2.1,order]
  have fHighV : q.c*(-13/50)<q.loV+q.side := by linarith only [elbow.2.2.2,cp,sn]
  have fGap := (short_projections q (13/50) (-1/2) (by norm_num)).2.1
  have fLowV : q.loV<q.c*(-13/50) := by linarith only [xUpperV,side,fGap]
  have fLowerU : q.s*(-13/50)≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro low (And.intro fHighU (And.intro fLowV fHighV))
  have tLowU : q.loU<q.c*(1/2)-q.s := by linarith only [marker.1,cp,sn]
  have tLowV : q.loV< -q.s*(1/2)-q.c := by linarith only [xUpperV,side,cu]
  have tHighV : -q.s*(1/2)-q.c<q.loV+q.side := by linarith only [elbow.2.2.2,cp,order]
  have tUpperU : q.loU+q.side≤q.c*(1/2)-q.s := by
    apply le_of_not_gt
    intro high
    apply missingT
    simpa only [OpenSquare.Inside,InBands,mul_neg_one] using
      And.intro tLowU (And.intro high (And.intro tLowV tHighV))
  have short := (short_projections q (1/2) (-37/50) (by norm_num)).2.1
  linarith only [fLowerU,tUpperU,side,short]

theorem horizontal (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingF : ¬q.Inside 0 (-13/50)) (missingT : ¬q.Inside (1/2) (-1)) :
    q.Inside (1/2) 0 := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have m := (same _ _).mpr marker
  have d := (same _ _).mpr elbow
  have a := (same _ _).mpr outer
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (horizontal_positive r cp sign
      (by simpa only [abs_of_nonneg sign] using range) m d a)
  · exact (same _ _).mp (horizontal_negative r (by simpa only [shape] using side)
      cp (le_of_not_ge sign) (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)
      m d a (fun h => missingF ((same _ _).mp h)) (fun h => missingT ((same _ _).mp h)))

private theorem upper_positive (q : OpenSquare)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) :
    q.Inside (21/40) (1/8) := by
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [elbow.1,cp,sn]
  · linarith only [outer.2.1,cp,order]
  · linarith only [marker.2.2.1,cp,order]
  · linarith only [upper.2.2.2,cp,sn]

private theorem upper_negative (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) (missingF : ¬q.Inside 0 (-13/50)) :
    q.Inside (21/40) (1/8) := by
  have yLowU : q.loU<q.c*(21/40)+q.s*(1/8) := by linarith only [elbow.1,cp,order]
  have yHighU : q.c*(21/40)+q.s*(1/8)<q.loU+q.side := by
    linarith only [outer.2.1,cp,sn]
  have yLowV : q.loV< -q.s*(21/40)+q.c*(1/8) := by
    linarith only [marker.2.2.1,cp,sn]
  have fLowU : q.loU<q.s*(-13/50) := by linarith only [upper.1,sn]
  have fHighU : q.s*(-13/50)<q.loU+q.side := by linarith only [outer.2.1,cp]
  have fHighV : q.c*(-13/50)<q.loV+q.side := by linarith only [upper.2.2.2,cp]
  have fLowerV : q.c*(-13/50)≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingF
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add] using
      And.intro fLowU (And.intro fHighU (And.intro low fHighV))
  have short := (short_projections q (21/40) (77/200) (by norm_num)).2.2.2
  have yHighV : -q.s*(21/40)+q.c*(1/8)<q.loV+q.side := by
    linarith only [fLowerV,side,short]
  exact ⟨yLowU,yHighU,yLowV,yHighV⟩

theorem upper (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) (missingF : ¬q.Inside 0 (-13/50)) :
    q.Inside (21/40) (1/8) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have m := (same _ _).mpr marker
  have d := (same _ _).mpr elbow
  have a := (same _ _).mpr outer
  have b := (same _ _).mpr upper
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (upper_positive r cp sign
      (by simpa only [abs_of_nonneg sign] using range) m d a b)
  · exact (same _ _).mp (upper_negative r (by simpa only [shape] using side)
      cp (le_of_not_ge sign) (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)
      m d a b (fun h => missingF ((same _ _).mp h)))

theorem horizontal_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (33/20))
    (elbow : q.Inside (113/50) 2) (outer : q.Inside 3 (87/50))
    (missingF : ¬q.Inside 2 (87/50)) (missingT : ¬q.Inside (5/2) 1) :
    q.Inside (5/2) 2 := by
  have point := horizontal (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact outer)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingT)
  norm_num [inside_translated_iff] at point
  exact point

theorem upper_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (33/20))
    (elbow : q.Inside (113/50) 2) (outer : q.Inside 3 (87/50))
    (upper : q.Inside 2 (113/50)) (missingF : ¬q.Inside 2 (87/50)) :
    q.Inside (101/40) (17/8) := by
  have point := F4PointTransfers.upper (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact outer)
    (by norm_num [inside_translated_iff]; exact upper)
    (by norm_num [inside_translated_iff]; exact missingF)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms horizontal_original
#print axioms upper_original
end N12Compact.Completion.OtherCases.F4PointTransfers

