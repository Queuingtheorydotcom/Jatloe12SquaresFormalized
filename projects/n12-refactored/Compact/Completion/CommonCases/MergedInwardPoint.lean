import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! MERGED-RIGHT-PATTERN-4 Theorem B. Its sharp foreign NW point
forces the merged owner to contain the southwest duplicate point. -/
namespace N12Compact.CommonCases.MergedInwardPoint
open S12 S12Pilot
set_option Elab.async false

private theorem negative_impossible (q : OpenSquare) (t : ℝ) (signed : q.s=-t)
    (side : 1 < q.side) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (p : q.Inside (7/20) (-7/20)) (upper : q.Inside (7/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingF : ¬q.Inside 0 (-13/50))
    (missingE : ¬q.Inside (1/6) (121/300)) : False := by
  simp only [OpenSquare.Inside,InBands,signed,mul_zero,zero_add,add_zero,neg_neg]
    at p upper h missingF missingE
  have fLowU : q.loU < (-t)*(-13/50) := by linarith only [h.1,tn]
  have fHighU : (-t)*(-13/50) < q.loU+q.side := by linarith only [p.2.1,cp,tn]
  have fHighV : q.c*(-13/50) < q.loV+q.side := by linarith only [h.2.2.2,cp]
  have fFace : q.c*(-13/50) ≤ q.loV :=
    le_of_not_gt (fun own => missingF ⟨fLowU,fHighU,own,fHighV⟩)
  have eLowU : q.loU < q.c*(1/6)+(-t)*(121/300) := by
    linarith only [h.1,cp,order]
  have eHighU : q.c*(1/6)+(-t)*(121/300) < q.loU+q.side := by
    linarith only [upper.2.1,cp,tn]
  have eLowV : q.loV < t*(1/6)+q.c*(121/300) := by
    linarith only [h.2.2.1,cp,tn]
  have eFace : q.loV+q.side ≤ t*(1/6)+q.c*(121/300) :=
    le_of_not_gt (fun own => missingE ⟨eLowU,eHighU,eLowV,own⟩)
  have short := (short_projections q (199/300) (-1/6) (by norm_num)).2.1
  rw [signed] at short
  linarith only [fFace,eFace,side,short]

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (p : q.Inside (7/20) (-7/20)) (upper : q.Inside (7/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingF : ¬q.Inside 0 (-13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingR : ¬q.Inside (543/500) 0)
    (missingE : ¬q.Inside (1/6) (121/300)) : q.Inside (-1/20) (-1/20) := by
  classical
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero,mul_one]
    at missingF missingJ missingR
  have cu := (CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have fHighU : q.s*(-13/50) < q.loU+q.side := by linarith only [h.2.1,sn]
  have fLowV : q.loV < q.c*(-13/50) := by linarith only [p.2.2.1,cp,sn]
  have fHighV : q.c*(-13/50) < q.loV+q.side := by linarith only [h.2.2.2,cp]
  have fFace : q.s*(-13/50) ≤ q.loU :=
    le_of_not_gt (fun own => missingF ⟨own,fHighU,fLowV,fHighV⟩)
  have jLowU : q.loU < q.c+q.s*(-13/50) := by linarith only [p.1,cp,sn]
  have jHighU : q.c+q.s*(-13/50) < q.loU+q.side := by linarith only [fFace,side,cu]
  have jHighV : -q.s+q.c*(-13/50) < q.loV+q.side := by linarith only [h.2.2.2,cp,sn]
  have jFace : -q.s+q.c*(-13/50) ≤ q.loV :=
    le_of_not_gt (fun own => missingJ ⟨jLowU,jHighU,own,jHighV⟩)
  have eLowU : q.loU < q.c*(1/6)+q.s*(121/300) := by linarith only [h.1,cp,sn]
  have eHighU : q.c*(1/6)+q.s*(121/300) < q.loU+q.side := by
    linarith only [upper.2.1,cp,order]
  have eLowV : q.loV < -q.s*(1/6)+q.c*(121/300) := by linarith only [p.2.2.1,cp,sn]
  have eFace : q.loV+q.side ≤ -q.s*(1/6)+q.c*(121/300) :=
    le_of_not_gt (fun own => missingE ⟨eLowU,eHighU,eLowV,own⟩)
  have span : 1 < (199/300)*q.c+(5/6)*q.s := by linarith only [jFace,eFace,side]
  have cutoff : (175/337)*q.c < (288/337)*q.s := by
    by_contra bad
    have short := CanonicalProjection.before q.c q.s (288/337) (175/337) (199/300) (5/6)
      q.unit_normal (by norm_num) (by exact le_of_not_gt bad) (by norm_num) (by norm_num)
    norm_num at short
    linarith only [span,short]
  have rLowU : q.loU < q.c*(543/500) := by linarith only [p.1,cp,sn]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by linarith only [h.2.2.2,cp,sn]
  have rLowV : q.loV < -q.s*(543/500) := by
    have short := OutwardScalars.increasing_projection q.c q.s (121/300) (1379/1500)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    linarith only [eFace,side,short]
  have rFace : q.loU+q.side ≤ q.c*(543/500) :=
    le_of_not_gt (fun own => missingR ⟨rLowU,own,rLowV,rHighV⟩)
  have lowU := CanonicalProjection.after q.c q.s (288/337) (175/337) (142/125) (1/20)
    q.unit_normal (by norm_num) cutoff.le (by norm_num) (by norm_num)
  norm_num at lowU
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [rFace,side,lowU]
  · linarith only [h.2.1,cp,sn]
  · linarith only [eFace,side,cu,sn]
  · linarith only [h.2.2.2,cp,order]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (7/20) (-7/20)) (upper : q.Inside (7/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingF : ¬q.Inside 0 (-13/50))
    (missingJ : ¬q.Inside 1 (-13/50)) (missingR : ¬q.Inside (543/500) 0)
    (missingE : ¬q.Inside (1/6) (121/300)) : q.Inside (-1/20) (-1/20) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have pp := (same _ _).mpr p
  have uu := (same _ _).mpr upper
  have hh := (same _ _).mpr h
  have f : ¬r.Inside 0 (-13/50) := fun own => missingF ((same _ _).mp own)
  have j : ¬r.Inside 1 (-13/50) := fun own => missingJ ((same _ _).mp own)
  have rr : ¬r.Inside (543/500) 0 := fun own => missingR ((same _ _).mp own)
  have e : ¬r.Inside (1/6) (121/300) := fun own => missingE ((same _ _).mp own)
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) pp uu hh f j rr e)
  · exact False.elim (negative_impossible r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) pp uu hh f e)

theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (47/20) (33/20)) (upper : q.Inside (47/20) (47/20))
    (h : q.Inside 2 (113/50)) (missingF : ¬q.Inside 2 (87/50))
    (missingJ : ¬q.Inside 3 (87/50)) (missingR : ¬q.Inside (1543/500) 2)
    (missingE : ¬q.Inside (13/6) (721/300)) : q.Inside (39/20) (39/20) := by
  have answer := point (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact p)
    (by norm_num [inside_translated_iff]; exact upper)
    (by norm_num [inside_translated_iff]; exact h)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingJ)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact missingE)
  norm_num [inside_translated_iff] at answer
  exact answer

#print axioms point_original
end N12Compact.CommonCases.MergedInwardPoint
