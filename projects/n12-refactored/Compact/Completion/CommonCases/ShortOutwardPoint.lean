import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The shorter actual top endpoint 2.73 forces the stronger outward
strict point 2.54,1.99 (C981-WALL-CYCLES, Theorem 9). -/
namespace N12Compact.CommonCases.ShortOutwardPoint
open S12 S12Pilot
set_option Elab.async false

theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingF : ¬q.Inside (13/50) 1)
    (missingT : ¬q.Inside (73/100) 1)
    (missingP : ¬q.Inside 1 1)
    (missingH : ¬q.Inside (543/500) 1) : q.Inside (27/50) (-1/100) := by
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
    have tLowU : q.loU < q.c*(73/100)+q.s := by
      linarith only [marker.1,cp,sn]
    have tLowV : q.loV < -q.s*(73/100)+q.c := by
      linarith only [marker.2.2.1,cp,order]
    have tHighV : -q.s*(73/100)+q.c < q.loV+q.side := by
      linarith only [low,side,cu,sn]
    have tFace : q.loU+q.side ≤ q.c*(73/100)+q.s :=
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
  have kHighU : q.c*(27/50)+q.s*(-1/100) < q.loU+q.side := by
    linarith only [outward.2.1,cp,sn]
  have kHighV : -q.s*(27/50)+q.c*(-1/100) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have tLowU : q.loU < q.c*(73/100)+q.s := by
    linarith only [marker.1,cp,sn]
  have tLowV : q.loV < -q.s*(73/100)+q.c := by
    linarith only [marker.2.2.1,cp,order]
  have kLowU : q.loU < q.c*(27/50)+q.s*(-1/100) := by
    by_cases topU : q.loU+q.side ≤ q.c*(73/100)+q.s
    · have short := OutwardScalars.increasing_projection q.c q.s (19/100) (101/100)
        cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
      linarith only [topU,short,side]
    · have topU' : q.c*(73/100)+q.s < q.loU+q.side := lt_of_not_ge topU
      have topV : q.loV+q.side ≤ -q.s*(73/100)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,topU',tLowV,h⟩)
      have span : 1 < q.c+(89/250)*q.s := by linarith only [topV,rFace,side]
      have short := OutwardScalars.short_strong_projection q.c q.s cp sp order q.unit_normal span
      linarith only [pFace,short,side]
  have kLowV : q.loV < -q.s*(27/50)+q.c*(-1/100) := by
    by_cases steep : 27*q.c ≤ 46*q.s
    · linarith only [outward.2.2.1,steep]
    · have shallow : 46*q.s ≤ 27*q.c := (lt_of_not_ge steep).le
      have sineHigh : q.s < 51/100 := by
        have ratio := mul_nonneg
          (show 0 ≤ 27*q.c-46*q.s by linarith only [shallow])
          (show 0 ≤ 27*q.c+46*q.s by linarith only [cp,sn])
        nlinarith only [q.unit_normal,ratio,sn]
      have tHighU : q.c*(73/100)+q.s < q.loU+q.side := by
        linarith only [gFace,side,cu,sineHigh]
      have tFace : q.loV+q.side ≤ -q.s*(73/100)+q.c :=
        le_of_not_gt (fun h => missingT ⟨tLowU,tHighU,tLowV,h⟩)
      linarith only [tFace,side,cu,sineLow]
  exact ⟨kLowU,kHighU,kLowV,kHighV⟩

theorem positive_point_original (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (47/20)) (outward : q.Inside 3 (113/50))
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingF : ¬q.Inside (113/50) 3)
    (missingT : ¬q.Inside (273/100) 3)
    (missingP : ¬q.Inside 3 3)
    (missingH : ¬q.Inside (1543/500) 3) : q.Inside (127/50) (199/100) := by
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
end N12Compact.CommonCases.ShortOutwardPoint
