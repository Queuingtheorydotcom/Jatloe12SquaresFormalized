import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The merged bottom owner in C982 has a forced negative angle and reaches
the endpoint of the obstructing segment. Every premise concerns its actual
open interior; exterior points may lie on a face. The argument is continuous.
Source written for the final assembled replay; not independently compiled. -/
namespace N12Compact.C982Merged

open S12 S12Pilot
set_option Elab.async false

private theorem positive_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (bottom : q.Inside 0 (-543/500))
    (central : q.Inside (-7/20) (-7/20))
    (missingJ : ¬ q.Inside (-13/50) (-1))
    (missingR : ¬ q.Inside (7/20) (-7/20)) : False := by
  have jUhi : q.c*(-13/50)+q.s*(-1) < q.loU+q.side := by
    linarith only [bottom.2.1,hc,order]
  have jVlo : q.loV < -q.s*(-13/50)+q.c*(-1) := by
    linarith only [bottom.2.2.1,hc,hs]
  have jVhi : -q.s*(-13/50)+q.c*(-1) < q.loV+q.side := by
    linarith only [central.2.2.2,hc,hs]
  have jFace : q.c*(-13/50)+q.s*(-1) ≤ q.loU :=
    le_of_not_gt (fun h => missingJ ⟨h,jUhi,jVlo,jVhi⟩)
  have rUlo : q.loU < q.c*(7/20)+q.s*(-7/20) := by
    linarith only [central.1,hc]
  have rVlo : q.loV < -q.s*(7/20)+q.c*(-7/20) := by
    linarith only [bottom.2.2.1,hc,order]
  have rVhi : -q.s*(7/20)+q.c*(-7/20) < q.loV+q.side := by
    linarith only [central.2.2.2,hs]
  have rFace : q.loU+q.side ≤ q.c*(7/20)+q.s*(-7/20) :=
    le_of_not_gt (fun h => missingR ⟨rUlo,h,rVlo,rVhi⟩)
  have short := (short_projections q (61/100) (13/20) (by norm_num)).2.1
  linarith only [jFace,rFace,short,side]

/-- The exact forced faces and strict angle bounds. The sine in the frame
is `-t`; no reflection of the geometric configuration is performed. -/
theorem negative_faces (q : OpenSquare) (t : ℝ) (signed : q.s = -t)
    (side : 1 < q.side) (hc : 0 < q.c) (ht : 0 ≤ t) (order : t ≤ q.c)
    (bottom : q.Inside 0 (-543/500))
    (central : q.Inside (-7/20) (-7/20))
    (missingJ : ¬ q.Inside (-13/50) (-1))
    (missingR : ¬ q.Inside (7/20) (-7/20)) :
    -(13/50)*t-q.c ≤ q.loV ∧
      q.loU+q.side ≤ (7/20)*(q.c+t) ∧
      43*q.c < 130*t ∧ 368*t < 175*q.c := by
  have b := bottom
  have m := central
  simp only [OpenSquare.Inside,InBands,signed] at b m
  have jUlo : q.loU < q.c*(-13/50)+q.s*(-1) := by
    rw [signed]
    linarith only [m.1,hc,ht]
  have jUhi : q.c*(-13/50)+q.s*(-1) < q.loU+q.side := by
    rw [signed]
    linarith only [b.2.1,hc,ht]
  have jVhi : -q.s*(-13/50)+q.c*(-1) < q.loV+q.side := by
    rw [signed]
    linarith only [m.2.2.2,hc,order]
  have jFace : -q.s*(-13/50)+q.c*(-1) ≤ q.loV :=
    le_of_not_gt (fun h => missingJ ⟨jUlo,jUhi,h,jVhi⟩)
  have rUlo : q.loU < q.c*(7/20)+q.s*(-7/20) := by
    rw [signed]
    linarith only [m.1,hc]
  have rVlo : q.loV < -q.s*(7/20)+q.c*(-7/20) := by
    rw [signed]
    linarith only [b.2.2.1,hc,ht]
  have short := (short_projections q (61/100) (13/20) (by norm_num)).2.2.2
  have rVhi : -q.s*(7/20)+q.c*(-7/20) < q.loV+q.side := by
    linarith only [jFace,short,side]
  have rFace : q.loU+q.side ≤ q.c*(7/20)+q.s*(-7/20) :=
    le_of_not_gt (fun h => missingR ⟨rUlo,h,rVlo,rVhi⟩)
  rw [signed] at jFace rFace
  exact ⟨by linarith only [jFace],by linarith only [rFace],
    by linarith only [jFace,b.2.2.1],
    by linarith only [rFace,b.2.1]⟩

/-- A rational quadratic certificate replaces the derivative comparison
at the endpoint slope 175/368. -/
private theorem endpoint_span (c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (unit : c^2+t^2=1) (slope : 368*t ≤ 175*c) :
    (21/25)*c+(14/25)*t < 1 := by
  have half : 2*t ≤ c := by linarith only [slope,hc]
  have factor : 0 ≤ 173509*c-193060*t := by
    linarith only [half,hc]
  have product := mul_nonneg
    (show 0 ≤ 175*c-368*t by linarith only [slope]) factor
  have identity :
      10178^2*(c^2+t^2)-166049*(21*c+14*t)^2 =
        (175*c-368*t)*(173509*c-193060*t) := by ring
  rw [unit] at identity
  by_contra failed
  have large : 25 ≤ 21*c+14*t := by linarith only [failed]
  have square := mul_nonneg (sub_nonneg.mpr large)
    (show 0 ≤ 21*c+14*t+25 by linarith only [hc,ht])
  nlinarith only [identity,product,square]

private theorem negative_reach (q : OpenSquare) (t : ℝ) (signed : q.s = -t)
    (side : 1 < q.side) (hc : 0 < q.c) (ht : 0 ≤ t) (order : t ≤ q.c)
    (bottom : q.Inside 0 (-543/500))
    (central : q.Inside (-7/20) (-7/20))
    (missingJ : ¬ q.Inside (-13/50) (-1))
    (missingR : ¬ q.Inside (7/20) (-7/20)) :
    q.Inside (3/10) (-4/25) := by
  obtain ⟨lower,upper,tiltLow,tiltHigh⟩ :=
    negative_faces q t signed side hc ht order bottom central missingJ missingR
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have span := endpoint_span q.c t hc.le ht unit tiltHigh.le
  have short := (short_projections q (1/20) (-19/100) (by norm_num)).2.1
  simp only [OpenSquare.Inside,InBands,signed] at bottom central
  rw [signed] at short
  change q.loU < q.c*(3/10)+q.s*(-4/25) ∧
    q.c*(3/10)+q.s*(-4/25) < q.loU+q.side ∧
    q.loV < -q.s*(3/10)+q.c*(-4/25) ∧
    -q.s*(3/10)+q.c*(-4/25) < q.loV+q.side
  rw [signed]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [upper,short,side]
  · linarith only [bottom.2.1,tiltLow,hc]
  · linarith only [bottom.2.2.1,hc,ht]
  · linarith only [lower,span,side]

/-- The single endpoint needed for the complete C982 contradiction.
All square orientations, including axial and diagonal frames, are covered. -/
theorem reaches (q : OpenSquare) (side : 1 < q.side)
    (bottom : q.Inside 0 (-543/500))
    (central : q.Inside (-7/20) (-7/20))
    (missingJ : ¬ q.Inside (-13/50) (-1))
    (missingR : ¬ q.Inside (7/20) (-7/20)) :
    q.Inside (3/10) (-4/25) := by
  obtain ⟨r,hc,canonical,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have b := (equivalent 0 (-543/500)).mpr bottom
  have m := (equivalent (-7/20) (-7/20)).mpr central
  have j : ¬ r.Inside (-13/50) (-1) := fun h => missingJ ((equivalent _ _).mp h)
  have k : ¬ r.Inside (7/20) (-7/20) := fun h => missingR ((equivalent _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · exact (positive_impossible r side' hc sign
      (by simpa only [abs_of_nonneg sign] using canonical) b m j k).elim
  · have negative : r.s < 0 := lt_of_not_ge sign
    exact (equivalent _ _).mp (negative_reach r (-r.s) (by ring) side' hc
      (by linarith only [negative])
      (by simpa only [abs_of_neg negative] using canonical) b m j k)

/-- The same endpoint in the original container coordinates. -/
theorem reaches_original (q : OpenSquare) (side : 1 < q.side)
    (bottom : q.Inside 2 (457/500))
    (central : q.Inside (33/20) (33/20))
    (missingJ : ¬ q.Inside (87/50) 1)
    (missingR : ¬ q.Inside (47/20) (33/20)) :
    q.Inside (23/10) (46/25) := by
  have reach := reaches (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact bottom)
    (by norm_num [inside_translated_iff]; exact central)
    (by norm_num [inside_translated_iff]; exact missingJ)
    (by norm_num [inside_translated_iff]; exact missingR)
  norm_num [inside_translated_iff] at reach
  exact reach

#print axioms reaches_original
end N12Compact.C982Merged
