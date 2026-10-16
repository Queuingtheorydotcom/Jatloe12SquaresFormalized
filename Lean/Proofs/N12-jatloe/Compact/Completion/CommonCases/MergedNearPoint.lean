import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! OTHER-GEOMETRY Theorem 11, proved directly from forced faces. The
short-chord description is unnecessary: the four endpoint exclusions and
two strict vertical markers force its four band bounds algebraically. -/
namespace N12Compact.CommonCases.MergedNearPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (p : q.Inside (7/20) (-7/20)) (upper : q.Inside (7/20) (7/20))
    (missingF : ¬q.Inside 0 (-13/50)) (missingH : ¬q.Inside 0 (13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingG : ¬q.Inside 1 (13/50))
    (missingR : ¬q.Inside (543/500) 0) :
    q.Inside (-1/20) (-1/20) ∧ q.Inside (-1/20) (1/20) := by
  classical
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero,mul_one]
    at missingF missingH missingJ missingG missingR
  have cu := (CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have fHighU : q.s*(-13/50) < q.loU+q.side := by
    linarith only [upper.2.1,cp,sn]
  have fLowV : q.loV < q.c*(-13/50) := by
    linarith only [p.2.2.1,cp,sn]
  have fHighV : q.c*(-13/50) < q.loV+q.side := by
    linarith only [upper.2.2.2,cp,order]
  have fFace : q.s*(-13/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingF ⟨h,fHighU,fLowV,fHighV⟩)
  have jLowU : q.loU < q.c+q.s*(-13/50) := by
    linarith only [p.1,cp,sn]
  have jHighU : q.c+q.s*(-13/50) < q.loU+q.side := by
    linarith only [fFace,side,cu]
  have jHighV : -q.s+q.c*(-13/50) < q.loV+q.side := by
    linarith only [upper.2.2.2,cp,sn]
  have jFace : -q.s+q.c*(-13/50) ≤ q.loV :=
    le_of_not_gt (fun h => missingJ ⟨jLowU,jHighU,h,jHighV⟩)
  have hHighU : q.s*(13/50) < q.loU+q.side := by
    linarith only [upper.2.1,cp,sn]
  have hLowV : q.loV < q.c*(13/50) := by
    linarith only [p.2.2.1,cp,sn]
  have gLowU : q.loU < q.c+q.s*(13/50) := by
    linarith only [upper.1,cp,order]
  have gHighV : -q.s+q.c*(13/50) < q.loV+q.side := by
    linarith only [upper.2.2.2,cp,sn]
  have hFace : q.loV+q.side ≤ q.c*(13/50) := by
    by_contra bad
    have hHighV : q.c*(13/50) < q.loV+q.side := by exact lt_of_not_ge bad
    have hLowFace : q.s*(13/50) ≤ q.loU :=
      le_of_not_gt (fun h => missingH ⟨h,hHighU,hLowV,hHighV⟩)
    have slope : 61*q.s < 35*q.c := by linarith only [hLowFace,p.1]
    have gHighU : q.c+q.s*(13/50) < q.loU+q.side := by
      linarith only [hLowFace,side,cu]
    have gLowFace : -q.s+q.c*(13/50) ≤ q.loV :=
      le_of_not_gt (fun h => missingG ⟨gLowU,gHighU,h,gHighV⟩)
    linarith only [slope,gLowFace,p.2.2.1,cp]
  have gLowV : q.loV < -q.s+q.c*(13/50) := by
    linarith only [hFace,side,cu,order]
  have gFace : q.loU+q.side ≤ q.c+q.s*(13/50) :=
    le_of_not_gt (fun h => missingG ⟨gLowU,h,gLowV,gHighV⟩)
  have span : 1 < (13/25)*q.c+q.s := by linarith only [hFace,jFace,side]
  have cutoff : (228/397)*q.c < (325/397)*q.s := by
    by_contra bad
    have short := CanonicalProjection.before q.c q.s (325/397) (228/397) (13/25) 1
      q.unit_normal (by norm_num) (by exact le_of_not_gt bad) (by norm_num) (by norm_num)
    norm_num at short
    linarith only [span,short]
  have rLowU : q.loU < q.c*(543/500) := by linarith only [p.1,cp,sn]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by
    linarith only [upper.2.2.2,cp,sn]
  have rLowV : q.loV < -q.s*(543/500) := by
    have short := OutwardScalars.increasing_projection q.c q.s (13/50) (543/500)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    linarith only [hFace,short,side]
  have rFace : q.loU+q.side ≤ q.c*(543/500) :=
    le_of_not_gt (fun h => missingR ⟨rLowU,h,rLowV,rHighV⟩)
  have lowerUShort := CanonicalProjection.after q.c q.s (325/397) (228/397) (142/125) (1/20)
    q.unit_normal (by norm_num) cutoff.le (by norm_num) (by norm_num)
  have lowerUBound : (142/125)*q.c+(1/20)*q.s < 1 := by
    norm_num at lowerUShort
    linarith only [lowerUShort]
  have upperVBound := OutwardScalars.increasing_projection q.c q.s (31/100) (21/20)
    cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
  have target (z : ℝ) (lo : -1/20≤z) (hi : z≤1/20) : q.Inside (-1/20) z := by
    have cLow := mul_le_mul_of_nonneg_left lo cp.le
    have cHigh := mul_le_mul_of_nonneg_left hi cp.le
    have sLow := mul_le_mul_of_nonneg_left lo sn
    have sHigh := mul_le_mul_of_nonneg_left hi sn
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [rFace,side,lowerUBound,sLow]
    · linarith only [p.2.1,sHigh,order]
    · linarith only [p.2.2.1,cLow,cp,sn]
    · linarith only [jFace,side,upperVBound,cHigh]
  exact ⟨target _ le_rfl (by norm_num),target _ (by norm_num) le_rfl⟩

theorem points (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (7/20) (-7/20)) (upper : q.Inside (7/20) (7/20))
    (missingF : ¬q.Inside 0 (-13/50)) (missingH : ¬q.Inside 0 (13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingG : ¬q.Inside 1 (13/50))
    (missingR : ¬q.Inside (543/500) 0) :
    q.Inside (-1/20) (-1/20) ∧ q.Inside (-1/20) (1/20) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have pp := (same _ _).mpr p
  have uu := (same _ _).mpr upper
  have f : ¬r.Inside 0 (-13/50) := fun h => missingF ((same _ _).mp h)
  have h : ¬r.Inside 0 (13/50) := fun h => missingH ((same _ _).mp h)
  have j : ¬r.Inside 1 (-13/50) := fun h => missingJ ((same _ _).mp h)
  have g : ¬r.Inside 1 (13/50) := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside (543/500) 0 := fun h => missingR ((same _ _).mp h)
  by_cases sign : 0 ≤ r.s
  · have answer := positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) pp uu f h j g rr
    exact ⟨(same _ _).mp answer.1,(same _ _).mp answer.2⟩
  · let reflected := pullY (r.translated 0 (-4))
    have answer := positive reflected side' cp
      (by change 0 ≤ -r.s; linarith only [sign])
      (by change -r.s ≤ r.c; simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; exact uu)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; simpa only [neg_div] using pp)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; exact h)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; simpa only [neg_div] using f)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; exact g)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; simpa only [neg_div] using j)
      (by norm_num [reflected,inside_pullY,inside_translated_iff]; exact rr)
    norm_num [reflected,inside_pullY,inside_translated_iff] at answer
    have result : r.Inside (-1/20) (-1/20) ∧ r.Inside (-1/20) (1/20) := by
      simpa only [neg_div] using And.intro answer.2 answer.1
    exact ⟨(same _ _).mp result.1,(same _ _).mp result.2⟩

theorem points_original (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (47/20) (33/20)) (upper : q.Inside (47/20) (47/20))
    (missingF : ¬q.Inside 2 (87/50)) (missingH : ¬q.Inside 2 (113/50))
    (missingJ : ¬q.Inside 3 (87/50)) (missingG : ¬q.Inside 3 (113/50))
    (missingR : ¬q.Inside (1543/500) 2) :
    q.Inside (39/20) (39/20) ∧ q.Inside (39/20) (41/20) := by
  have answer := points (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact p)
    (by norm_num [inside_translated_iff]; exact upper)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingH)
    (by norm_num [inside_translated_iff]; exact missingJ)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
  norm_num [inside_translated_iff] at answer
  exact answer

#print axioms points_original
end N12Compact.CommonCases.MergedNearPoint
