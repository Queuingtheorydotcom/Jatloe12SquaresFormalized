import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import Compact.Completion.C981.OutwardAnchor

/-! The positive canonical outward square owns the same strict point as
InwardPoint. Every face is obtained from actual owned/excluded points. -/
namespace N12Compact.CommonCases.StrongBarPoint
open S12 S12Pilot
set_option Elab.async false

theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingF : ¬q.Inside (13/50) 1)
    (missingT : ¬q.Inside (43/50) 1)
    (missingH : ¬q.Inside (543/500) 1) : q.Inside (23/50) (-1/100) := by
  classical
  simp only [OpenSquare.Inside, InBands, mul_one, mul_zero, add_zero]
    at missingG missingR missingF missingT missingH ⊢
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
    have tLowU : q.loU < q.c*(43/50)+q.s := by
      linarith only [marker.1,cp,sn]
    have tLowV : q.loV < -q.s*(43/50)+q.c := by
      linarith only [marker.2.2.1,cp,order]
    have tHighV : -q.s*(43/50)+q.c < q.loV+q.side := by
      linarith only [low,side,cu,sn]
    have tFace : q.loU+q.side ≤ q.c*(43/50)+q.s :=
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
  have kHighU : q.c*(23/50)+q.s*(-1/100) < q.loU+q.side := by
    linarith only [outward.2.1,cp,sn]
  have kHighV : -q.s*(23/50)+q.c*(-1/100) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have tLowU : q.loU < q.c*(43/50)+q.s := by
    linarith only [marker.1,cp,sn]
  have tLowV : q.loV < -q.s*(43/50)+q.c := by
    linarith only [marker.2.2.1,cp,order]
  have kLowU : q.loU < q.c*(23/50)+q.s*(-1/100) := by
    by_cases topU : q.loU+q.side ≤ q.c*(43/50)+q.s
    · have short := OutwardScalars.increasing_projection q.c q.s (2/5) (101/100)
        cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
      linarith only [topU,short,side]
    · have topU' : q.c*(43/50)+q.s < q.loU+q.side := lt_of_not_ge topU
      have topV : q.loV+q.side ≤ -q.s*(43/50)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,topU',tLowV,h⟩)
      have span : 1 < q.c+(113/500)*q.s := by linarith only [topV,rFace,side]
      have short := OutwardScalars.strong_bar_projection q.c q.s cp sp order q.unit_normal span
      linarith only [hFace,short,side]
  have kLowV : q.loV < -q.s*(23/50)+q.c*(-1/100) := by
    by_cases steep : q.c ≤ 2*q.s
    · linarith only [outward.2.2.1,steep]
    · have shallow : 2*q.s ≤ q.c := (lt_of_not_ge steep).le
      have short : (3/5)*q.c+q.s < 1 := by
        have product := mul_pos cp
          (show 0 < (16/25)*q.c-(6/5)*q.s by linarith only [shallow,cp])
        nlinarith only [q.unit_normal,product,cp,sn]
      have tHighU : q.c*(43/50)+q.s < q.loU+q.side := by
        linarith only [gFace,side,short]
      have tFace : q.loV+q.side ≤ -q.s*(43/50)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,tHighU,tLowV,h⟩)
      linarith only [tFace,side,cu,sineLow]
  exact ⟨kLowU,kHighU,kLowV,kHighV⟩

private theorem negative_corner_impossible (q : OpenSquare) (t : ℝ)
    (signed : q.s = -t) (side : 1 < q.side) (cp : 0 < q.c)
    (tn : 0 ≤ t) (order : t ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (corner : q.Inside 3 3)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingT : ¬q.Inside (143/50) 3) : False := by
  have m := marker
  have p := corner
  simp only [OpenSquare.Inside,InBands,signed] at m p
  have tHighU : q.c*(143/50)+q.s*3 < q.loU+q.side := by
    rw [signed]; linarith only [p.2.1,cp]
  have tLowV : q.loV < -q.s*(143/50)+q.c*3 := by
    rw [signed]; linarith only [m.2.2.1,cp,tn]
  have tHighV : -q.s*(143/50)+q.c*3 < q.loV+q.side := by
    rw [signed]; linarith only [p.2.2.2,tn]
  have tFace : q.c*(143/50)+q.s*3 ≤ q.loU :=
    le_of_not_gt (fun h => missingT ⟨h,tHighU,tLowV,tHighV⟩)
  have slope : 51*q.c < 65*t := by
    rw [signed] at tFace
    linarith only [tFace,m.1]
  have rLowU : q.loU < q.c*(1543/500)+q.s*2 := by
    rw [signed]; linarith only [m.1,cp,tn]
  have rLowV : q.loV < -q.s*(1543/500)+q.c*2 := by
    rw [signed]; linarith only [m.2.2.1,slope,cp]
  have rHighV : -q.s*(1543/500)+q.c*2 < q.loV+q.side := by
    rw [signed]; linarith only [p.2.2.2,cp,order]
  have rFace : q.loU+q.side ≤ q.c*(1543/500)+q.s*2 :=
    le_of_not_gt (fun h => missingR ⟨rLowU,h,rLowV,rHighV⟩)
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have short := OutwardScalars.increasing_projection q.c t (113/500) 1
    cp tn order unit (by norm_num) (by norm_num) (by norm_num)
  rw [signed] at tFace rFace
  linarith only [tFace,rFace,side,short]

theorem positive_point_original (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (outward : q.Inside 3 (113/50))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 143/50 → ¬q.Inside z 3) :
    q.Inside (123/50) (199/100) := by
  classical
  have h := positive_point (q.translated 2 2) side cp sn order
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact outward)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact avoid _ le_rfl (by norm_num))
    (by norm_num [inside_translated_iff]; exact avoid _ (by norm_num) le_rfl)
    (by norm_num [inside_translated_iff]; exact missingH)
  norm_num [inside_translated_iff] at h
  exact h

/-- Full OUTWARD-STRONG-BAR theorem. The corner point (3,3) is never
introduced as an exclusion; both of its actual ownership alternatives are
handled in the nonpositive frame. -/
theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20))
    (outward : q.Inside 3 (113/50)) (upper : q.Inside 3 (12/5))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 143/50 → ¬q.Inside z 3) :
    q.Inside (123/50) (199/100) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr outward
  have b := (same _ _).mpr upper
  have g : ¬r.Inside (113/50) 2 := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside (1543/500) 2 := fun h => missingR ((same _ _).mp h)
  have h : ¬r.Inside (1543/500) 3 := fun h => missingH ((same _ _).mp h)
  have segment (z : ℝ) (low : 113/50 ≤ z) (high : z ≤ 143/50) : ¬r.Inside z 3 :=
    fun own => avoid z low high ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive_point_original r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m a g rr h segment)
  · exfalso
    by_cases corner : r.Inside 3 3
    · exact negative_corner_impossible r (-r.s) (by ring) side' cp
        (by linarith only [sign])
        (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
        m corner rr (segment _ (by norm_num) le_rfl)
    · apply C981CompletionOutwardAnchor.nonnegative_impossible (pullY r) side' cp
        (by change 0 ≤ -r.s; linarith only [sign])
        (by change -r.s ≤ r.c; simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
      · norm_num [inside_pullY]; exact m
      · norm_num [inside_pullY]; exact b
      · norm_num [inside_pullY]; exact corner
      · norm_num [inside_pullY]; exact rr
      · norm_num [inside_pullY]; exact g
      · intro z low high own
        exact segment z low (by linarith only [high])
          (by norm_num [inside_pullY] at own; exact own)

#print axioms point_original
end N12Compact.CommonCases.StrongBarPoint
