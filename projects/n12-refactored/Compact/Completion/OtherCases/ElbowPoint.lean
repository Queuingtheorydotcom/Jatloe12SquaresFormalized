import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The full three-anchor elbow transfer, with all signed canonical
orientations. The exact three omitted points fix both upper faces. -/
namespace N12Compact.Completion.OtherCases.ElbowPoint
open S12 S12Pilot
set_option Elab.async false

theorem positive_impossible (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (outer : q.Inside 1 (-13/50))
    (missingN : ¬q.Inside (7/20) (7/20))
    (missingG : ¬q.Inside 1 (-2/5)) : False := by
  have nLowU : q.loU<q.c*(7/20)+q.s*(7/20) := by linarith only [marker.1,sn]
  have nHighU : q.c*(7/20)+q.s*(7/20)<q.loU+q.side := by
    linarith only [outer.2.1,cp,order]
  have nLowV : q.loV< -q.s*(7/20)+q.c*(7/20) := by
    linarith only [marker.2.2.1,cp]
  have nUpperV : q.loV+q.side≤ -q.s*(7/20)+q.c*(7/20) :=
    le_of_not_gt (fun h => missingN ⟨nLowU,nHighU,nLowV,h⟩)
  have gLowU : q.loU<q.c+q.s*(-2/5) := by linarith only [marker.1,cp,order]
  have gHighU : q.c+q.s*(-2/5)<q.loU+q.side := by linarith only [outer.2.1,sn]
  have gHighV : -q.s+q.c*(-2/5)<q.loV+q.side := by linarith only [outer.2.2.2,cp]
  have gLowerV : -q.s+q.c*(-2/5)≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingG
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro gLowU (And.intro gHighU (And.intro low gHighV))
  have short := (short_projections q (-13/20) (3/4) (by norm_num)).2.2.2
  linarith only [nUpperV,gLowerV,side,short]

theorem negative_faces (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingN : ¬q.Inside (7/20) (7/20))
    (missingG : ¬q.Inside 1 (-2/5)) (missingR : ¬q.Inside (543/500) 0) :
    q.loU+q.side≤q.c-(2/5)*q.s ∧
      q.loV+q.side≤(7/20)*(q.c-q.s) := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have nHighU : q.c*(7/20)+q.s*(7/20)<q.loU+q.side := by
    linarith only [outer.2.1,cp,sn]
  have nLowV : q.loV< -q.s*(7/20)+q.c*(7/20) := by linarith only [marker.2.2.1,cp]
  have gLowU : q.loU<q.c+q.s*(-2/5) := by linarith only [marker.1,cp,sn]
  have gHighV : -q.s+q.c*(-2/5)<q.loV+q.side := by linarith only [outer.2.2.2,cp]
  have nUpperV : q.loV+q.side≤ -q.s*(7/20)+q.c*(7/20) := by
    apply le_of_not_gt
    intro nHighV
    have nLowerU : q.c*(7/20)+q.s*(7/20)≤q.loU :=
      le_of_not_gt (fun h => missingN ⟨h,nHighU,nLowV,nHighV⟩)
    have shortG := (short_projections q (13/20) (-3/4) (by norm_num)).2.1
    have gHighU : q.c+q.s*(-2/5)<q.loU+q.side := by linarith only [nLowerU,side,shortG]
    have gLowerV : -q.s+q.c*(-2/5)≤q.loV := by
      apply le_of_not_gt
      intro low
      apply missingG
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro gLowU (And.intro gHighU (And.intro low gHighV))
    have rLowU : q.loU<q.c*(543/500) := by linarith only [elbow.1,cp]
    have rLowV : q.loV< -q.s*(543/500) := by linarith only [elbow.2.2.1,sn]
    have shortRU := (short_projections q (92/125) (-7/20) (by norm_num)).2.1
    have rHighU : q.c*(543/500)<q.loU+q.side := by linarith only [nLowerU,side,shortRU]
    have shortRV := (short_projections q (43/500) (2/5) (by norm_num)).2.2.2
    have rHighV : -q.s*(543/500)<q.loV+q.side := by linarith only [gLowerV,side,shortRV]
    apply missingR
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero] using
      And.intro rLowU (And.intro rHighU (And.intro rLowV rHighV))
  have gLowV : q.loV< -q.s+q.c*(-2/5) := by linarith only [nUpperV,side,cu,sn]
  have gUpperU : q.loU+q.side≤q.c+q.s*(-2/5) := by
    apply le_of_not_gt
    intro high
    apply missingG
    simpa only [OpenSquare.Inside,InBands,mul_one] using
      And.intro gLowU (And.intro high (And.intro gLowV gHighV))
  exact ⟨by linarith only [gUpperU],by linarith only [nUpperV]⟩

theorem points (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingN : ¬q.Inside (7/20) (7/20))
    (missingG : ¬q.Inside 1 (-2/5)) (missingR : ¬q.Inside (543/500) 0) :
    q.Inside 0 (-1/2) ∧ q.Inside (1/8) (-21/40) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have d := (same _ _).mpr elbow
  have a := (same _ _).mpr outer
  have n : ¬r.Inside (7/20) (7/20) := fun h => missingN ((same _ _).mp h)
  have g : ¬r.Inside 1 (-2/5) := fun h => missingG ((same _ _).mp h)
  by_cases sign : 0≤r.s
  · exact False.elim (positive_impossible r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range) m a n g)
  · have sn : r.s≤0 := le_of_not_ge sign
    have order : -r.s≤r.c := by simpa only [abs_of_neg (lt_of_not_ge sign)] using range
    have faces := negative_faces r side' cp sn order m d a n g
      (fun h => missingR ((same _ _).mp h))
    have cu : r.c≤1 := by nlinarith only [r.unit_normal,sq_nonneg r.s,cp]
    have xShort := (short_projections r (7/20) (17/20) (by norm_num)).2.2.2
    have yShort := (short_projections r (9/40) (7/8) (by norm_num)).2.2.2
    have first : r.Inside 0 (-1/2) := by
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [faces.1,side',cu,sn]
      · linarith only [m.2.1,cp,order]
      · linarith only [faces.2,side',xShort]
      · linarith only [m.2.2.2,cp,sn]
    have second : r.Inside (1/8) (-21/40) := by
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [faces.1,side',cu,sn]
      · linarith only [m.2.1,cp,order]
      · linarith only [faces.2,side',yShort]
      · linarith only [m.2.2.2,cp,sn]
    exact ⟨(same _ _).mp first,(same _ _).mp second⟩

theorem points_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (33/20))
    (elbow : q.Inside (113/50) 2) (outer : q.Inside 3 (87/50))
    (missingN : ¬q.Inside (47/20) (47/20))
    (missingG : ¬q.Inside 3 (8/5)) (missingR : ¬q.Inside (1543/500) 2) :
    q.Inside 2 (3/2) ∧ q.Inside (17/8) (59/40) := by
  have point := points (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact outer)
    (by norm_num [inside_translated_iff]; exact missingN)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
  norm_num [inside_translated_iff] at point
  exact point

#print axioms points_original
end N12Compact.Completion.OtherCases.ElbowPoint

