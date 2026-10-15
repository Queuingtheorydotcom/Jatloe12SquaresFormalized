import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! `ELBOW-CROSSPOINT.md`, Theorems 2 and 3.
The crossed-elbow obstruction uses three isolated exclusions, including
every w in the entire closed interval [1/2,4/5]. The fourth-anchor theorem
produces the exact common sharp point. Neither theorem assumes a wall,
side cap, marker absence, foreign segment, or square center.
All square orientations and weak excluded-face contacts are retained.
This is source translation only; no compiler or replay was run. -/
namespace N12Compact.Completion.OtherCases.CrossedElbow
open S12 S12Pilot
set_option Elab.async false

private theorem positive_crosspoint (q : OpenSquare)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50)) :
    q.Inside (1/2) 0 := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [elbow.1,outer.2.1,marker.2.2.1,elbow.2.2.2,cp,sn,order]

private theorem negative_impossible (q : OpenSquare) (w : ℝ)
    (side : 1<q.side) (wLow : 1/2≤w) (wHigh : w≤4/5)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingX : ¬q.Inside (1/2) 0) (missingC : ¬q.Inside 0 (-1/2))
    (missingT : ¬q.Inside w (-1)) : False := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have tn : 0≤ -q.s := by linarith only [sn]
  have upperV : q.loV+q.side≤-q.s/2 := by
    apply le_of_not_gt
    intro high
    apply missingX
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,elbow.1,elbow.2.2.1,outer.2.1,cp,sn]
  have slope : 25*(-q.s)<13*q.c := by linarith only [outer.2.2.2,upperV]
  have halfSum := (short_projections q (1/2) (1/2) (by norm_num)).2.2.2
  have lowerU : -q.s/2≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingC
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,elbow.2.1,elbow.2.2.2,slope,upperV,side,halfSum,cp,sn]
  have markerGap := mul_pos (show 0<w-7/20 by linarith only [wLow]) cp
  have highWeight := mul_le_mul_of_nonneg_right wHigh tn
  have lowWeight := mul_nonneg (sub_nonneg.mpr wLow) tn
  have upperU : q.loU+q.side≤q.c*w-q.s := by
    apply le_of_not_gt
    intro high
    apply missingT
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [high,marker.1,elbow.2.2.2,upperV,side,cu,
        markerGap,highWeight,lowWeight,cp,sn,order]
  have horizontal := mul_le_mul_of_nonneg_right wHigh cp.le
  have short := (short_projections q (4/5) (-1/2) (by norm_num)).2.1
  nlinarith only [lowerU,upperU,side,horizontal,short]

/-- Theorem 2, in coordinates translated by (-2,-2). The three
omissions are independent point facts; no interval between them is used. -/
theorem impossible (q : OpenSquare) (w : ℝ)
    (side : 1<q.side) (wLow : 1/2≤w) (wHigh : w≤4/5)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (missingX : ¬q.Inside (1/2) 0) (missingC : ¬q.Inside 0 (-1/2))
    (missingT : ¬q.Inside w (-1)) : False := by
  obtain ⟨r,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (inside _ _).mpr marker
  have d := (inside _ _).mpr elbow
  have a := (inside _ _).mpr outer
  have x : ¬r.Inside (1/2) 0 := fun own => missingX ((inside _ _).mp own)
  by_cases sign : 0≤r.s
  · exact x (positive_crosspoint r cp sign
      (by simpa only [abs_of_nonneg sign] using range) m d a)
  · exact negative_impossible r w side' wLow wHigh cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m d a x
      (fun own => missingC ((inside _ _).mp own))
      (fun own => missingT ((inside _ _).mp own))

private theorem positive_point (q : OpenSquare)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) : q.Inside (21/40) (1/8) := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [elbow.1,outer.2.1,marker.2.2.1,upper.2.2.2,cp,sn,order]

private theorem negative_point (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) (missingC : ¬q.Inside 0 (-1/2)) :
    q.Inside (21/40) (1/8) := by
  have lowerV : -q.c/2≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingC
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,upper.1,outer.2.1,upper.2.2.2,cp,sn,order]
  have short := (short_projections q (21/40) (5/8) (by norm_num)).2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [elbow.1,cp,order]
  · linarith only [outer.2.1,cp,sn]
  · linarith only [marker.2.2.1,cp,sn]
  · linarith only [lowerV,short,side]

/-- Theorem 3. A fourth strict anchor and one genuine point exclusion
give the sharp point for both canonical signs, including all endpoints. -/
theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20))
    (elbow : q.Inside (13/50) 0) (outer : q.Inside 1 (-13/50))
    (upper : q.Inside 0 (13/50)) (missingC : ¬q.Inside 0 (-1/2)) :
    q.Inside (21/40) (1/8) := by
  obtain ⟨r,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have m := (inside _ _).mpr marker
  have d := (inside _ _).mpr elbow
  have a := (inside _ _).mpr outer
  have f := (inside _ _).mpr upper
  apply (inside _ _).mp
  by_cases sign : 0≤r.s
  · exact positive_point r cp sign
      (by simpa only [abs_of_nonneg sign] using range) m d a f
  · exact negative_point r side' cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range) m d a f
      (fun own => missingC ((inside _ _).mp own))

theorem impossible_original (q : OpenSquare) (w : ℝ)
    (side : 1<q.side) (wLow : 1/2≤w) (wHigh : w≤4/5)
    (marker : q.Inside (47/20) (33/20))
    (elbow : q.Inside (113/50) 2) (outer : q.Inside 3 (87/50))
    (missingX : ¬q.Inside (5/2) 2) (missingC : ¬q.Inside 2 (3/2))
    (missingT : ¬q.Inside (2+w) 1) : False := by
  apply impossible (q.translated 2 2) w side wLow wHigh
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact outer)
    (by norm_num [inside_translated_iff]; exact missingX)
    (by norm_num [inside_translated_iff]; exact missingC)
  intro own
  have actual := (inside_translated_iff q 2 2 w (-1)).mp own
  apply missingT
  convert actual using 1 <;> ring

theorem point_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (33/20))
    (elbow : q.Inside (113/50) 2) (outer : q.Inside 3 (87/50))
    (upper : q.Inside 2 (113/50)) (missingC : ¬q.Inside 2 (3/2)) :
    q.Inside (101/40) (17/8) := by
  have result := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact outer)
    (by norm_num [inside_translated_iff]; exact upper)
    (by norm_num [inside_translated_iff]; exact missingC)
  norm_num [inside_translated_iff] at result
  exact result

#print axioms impossible
#print axioms point
#print axioms impossible_original
#print axioms point_original
end N12Compact.Completion.OtherCases.CrossedElbow
