import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import Compact.Completion.C981.OutwardAnchor

/-! The positive canonical outward square owns the same strict point as
InwardPoint. Every face is obtained from actual owned/excluded points. -/
namespace N12Compact.CommonCases.OutwardPoint
open S12 S12Pilot
set_option Elab.async false

theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingF : ¬q.Inside (13/50) 1)
    (missingT : ¬q.Inside (4/5) 1)
    (missingP : ¬q.Inside 1 1)
    (missingH : ¬q.Inside (543/500) 1) : q.Inside (23/50) (-1/100) := by
  classical
  simp only [OpenSquare.Inside, InBands, mul_one, mul_zero, add_zero]
    at missingG missingR missingF missingT missingP missingH ⊢
  have cu := (CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have gHighU : q.c*(13/50) < q.loU+q.side := by
    linarith only [marker.2.1,cp,sn]
  have gHighV : -q.s*(13/50) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have gLowV : q.loV < -q.s*(13/50) := by
    by_contra failed
    have low : -q.s*(13/50) ≤ q.loV := le_of_not_gt failed
    have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
      linarith only [outward.2.1,order]
    have fLowV : q.loV < -q.s*(13/50)+q.c := by
      linarith only [marker.2.2.1,cp,sn]
    have fHighV : -q.s*(13/50)+q.c < q.loV+q.side := by
      linarith only [low,side,cu]
    have fFace : q.c*(13/50)+q.s ≤ q.loU :=
      le_of_not_gt (fun h => missingF ⟨h,fHighU,fLowV,fHighV⟩)
    have tLowU : q.loU < q.c*(4/5)+q.s := by
      linarith only [marker.1,cp,sn]
    have tLowV : q.loV < -q.s*(4/5)+q.c := by
      linarith only [marker.2.2.1,cp,order]
    have tHighV : -q.s*(4/5)+q.c < q.loV+q.side := by
      linarith only [low,side,cu,sn]
    have tFace : q.loU+q.side ≤ q.c*(4/5)+q.s :=
      le_of_not_gt (fun h => missingT ⟨tLowU,h,tLowV,tHighV⟩)
    linarith only [fFace,tFace,side,cu]
  have gFace : q.c*(13/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingG ⟨h,gHighU,gLowV,gHighV⟩)
  have rLowU : q.loU < q.c*(543/500) := by
    linarith only [marker.1,cp,order]
  have rHighU : q.c*(543/500) < q.loU+q.side := by
    linarith only [gFace,side,cu]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by
    linarith only [outward.2.2.2,cp,sn]
  have rFace : -q.s*(543/500) ≤ q.loV :=
    le_of_not_gt (fun h => missingR ⟨rLowU,rHighU,h,rHighV⟩)
  have hLowU : q.loU < q.c*(543/500)+q.s := by
    linarith only [outward.1,cp,sn]
  have hLowV : q.loV < -q.s*(543/500)+q.c := by
    linarith only [outward.2.2.1,cp,order]
  have hHighV : -q.s*(543/500)+q.c < q.loV+q.side := by
    linarith only [rFace,side,cu]
  have hFace : q.loU+q.side ≤ q.c*(543/500)+q.s :=
    le_of_not_gt (fun h => missingH ⟨hLowU,h,hLowV,hHighV⟩)
  have sineLow : 87/500 < q.s := by linarith only [gFace,hFace,side,cu]
  have sp : 0 < q.s := (by norm_num : (0:ℝ) < 87/500).trans sineLow
  have cosineUpper : q.c ≤ 1-q.s^2/2 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-1)]
  have pLowU : q.loU < q.c+q.s := by
    linarith only [marker.1,cp,sn]
  have pLowV : q.loV < -q.s+q.c := by
    linarith only [marker.2.2.1,order]
  have pHighV : -q.s+q.c < q.loV+q.side := by
    have gap : q.c+(43/500)*q.s < 1 := by
      have product := mul_pos sp
        (show 0 < q.s-43/250 by linarith only [sineLow])
      nlinarith only [cosineUpper,product]
    linarith only [rFace,side,gap]
  have pFace : q.loU+q.side ≤ q.c+q.s :=
    le_of_not_gt (fun h => missingP ⟨pLowU,h,pLowV,pHighV⟩)
  have kHighU : q.c*(23/50)+q.s*(-1/100) < q.loU+q.side := by
    linarith only [outward.2.1,cp,sn]
  have kHighV : -q.s*(23/50)+q.c*(-1/100) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have tLowU : q.loU < q.c*(4/5)+q.s := by
    linarith only [marker.1,cp,sn]
  have tLowV : q.loV < -q.s*(4/5)+q.c := by
    linarith only [marker.2.2.1,cp,order]
  have kLowU : q.loU < q.c*(23/50)+q.s*(-1/100) := by
    by_cases topU : q.loU+q.side ≤ q.c*(4/5)+q.s
    · have short := OutwardScalars.increasing_projection q.c q.s (17/50) (101/100)
        cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
      linarith only [topU,short,side]
    · have topU' : q.c*(4/5)+q.s < q.loU+q.side := lt_of_not_ge topU
      have topV : q.loV+q.side ≤ -q.s*(4/5)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,topU',tLowV,h⟩)
      have span : 1 < q.c+(143/500)*q.s := by linarith only [topV,rFace,side]
      have short := OutwardScalars.shallow_projection q.c q.s cp sp order q.unit_normal span
      linarith only [pFace,short,side]
  have kLowV : q.loV < -q.s*(23/50)+q.c*(-1/100) := by
    by_cases steep : q.c ≤ 2*q.s
    · linarith only [outward.2.2.1,steep]
    · have shallow : 2*q.s ≤ q.c := (lt_of_not_ge steep).le
      have sineHigh : q.s < 9/20 := by
        have ratio := mul_nonneg
          (show 0 ≤ q.c-2*q.s by linarith only [shallow])
          (show 0 ≤ q.c+2*q.s by linarith only [cp,sn])
        nlinarith only [q.unit_normal,ratio,sn]
      have tHighU : q.c*(4/5)+q.s < q.loU+q.side := by
        linarith only [gFace,side,cu,sineHigh]
      have tFace : q.loV+q.side ≤ -q.s*(4/5)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,tHighU,tLowV,h⟩)
      linarith only [tFace,side,cu,sineLow]
  exact ⟨kLowU,kHighU,kLowV,kHighV⟩

theorem positive_point_original (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (outward : q.Inside 3 (113/50))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingF : ¬q.Inside (113/50) 3)
    (missingT : ¬q.Inside (14/5) 3)
    (missingP : ¬q.Inside 3 3)
    (missingH : ¬q.Inside (1543/500) 3) : q.Inside (123/50) (199/100) := by
  have h := positive_point (q.translated 2 2) side cp sn order
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact outward)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingT)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingH)
  norm_num [inside_translated_iff] at h
  exact h

#print axioms positive_point_original

/-- The signed canonical choice is discharged by the genuine foreign top
segment and paired-corner point. This conclusion covers every orientation. -/
theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20))
    (outward : q.Inside 3 (113/50)) (upper : q.Inside 3 (12/5))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3)
    (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬q.Inside z 3) :
    q.Inside (123/50) (199/100) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr outward
  have b := (same _ _).mpr upper
  have g : ¬r.Inside (113/50) 2 := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside (1543/500) 2 := fun h => missingR ((same _ _).mp h)
  have p : ¬r.Inside 3 3 := fun h => missingP ((same _ _).mp h)
  have h : ¬r.Inside (1543/500) 3 := fun h => missingH ((same _ _).mp h)
  have segment (z : ℝ) (low : 113/50 ≤ z) (high : z ≤ 14/5) : ¬r.Inside z 3 :=
    fun own => avoid z low high ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive_point_original r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m a g rr
      (segment _ le_rfl (by norm_num))
      (segment _ (by norm_num) le_rfl) p h)
  · exfalso
    apply C981CompletionOutwardAnchor.nonnegative_impossible (pullY r) side' cp
      (by change 0 ≤ -r.s; linarith only [sign])
      (by change -r.s ≤ r.c; simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
    · norm_num [inside_pullY]; exact m
    · norm_num [inside_pullY]; exact b
    · norm_num [inside_pullY]; exact p
    · norm_num [inside_pullY]; exact rr
    · norm_num [inside_pullY]; exact g
    · intro z low high own
      exact segment z low high (by norm_num [inside_pullY] at own; exact own)

#print axioms point_original
end N12Compact.CommonCases.OutwardPoint
