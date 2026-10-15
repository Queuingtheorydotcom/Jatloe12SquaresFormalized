import Compact.Geometry.WallLowerCenterBarrier
import Compact.Geometry.ThreeSquareSupport

/-! An inward auxiliary point constrains the actual center of a wall owner.
The upper central exclusion fixes two escape faces and a continuous normal
sector. The resulting rational center box has no numerical ancestry premise.
The square need not be contained in a container for this local lemma. -/
namespace N12Compact.WallInwardCenter
open S12 S12Pilot
set_option Elab.async false

private theorem positive_box (q : OpenSquare)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hD : q.Inside (87/50) 2)
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) :
    21/20 ≤ centerX q ∧ centerX q ≤ 7/4 ∧
      9/4 ≤ centerY q ∧ centerY q ≤ 59/20 := by
  have tUlo : q.loU < q.c*(33/20)+q.s*(47/20) := by
    nlinarith only [hP.1, hc, hs]
  have tVlo : q.loV < -q.s*(33/20)+q.c*(47/20) := by
    nlinarith only [hD.2.2.1, hc, hs]
  have tVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
    nlinarith only [hQ.2.2.2, hc, hs]
  have tu : q.loU+q.side ≤ q.c*(33/20)+q.s*(47/20) :=
    le_of_not_gt (fun upper => hT ⟨tUlo,upper,tVlo,tVhi⟩)
  have wUhi : q.c+q.s*(87/50) < q.loU+q.side := by
    nlinarith only [hQ.2.1, hs]
  have wVhi : -q.s+q.c*(87/50) < q.loV+q.side := by
    nlinarith only [hP.2.2.2, hc, hs]
  have gap := (short_projections q (13/20) (61/100) (by norm_num)).2.1
  have wUlo : q.loU < q.c+q.s*(87/50) := by
    apply lt_of_not_ge
    intro lower
    linarith only [lower,tu,gap,ha]
  have wv : -q.s+q.c*(87/50) ≤ q.loV := by
    apply le_of_not_gt
    intro lower
    apply hW
    exact ⟨by simpa only [mul_one] using wUlo,
      by simpa only [mul_one] using wUhi,
      by simpa only [mul_one] using lower,
      by simpa only [mul_one] using wVhi⟩
  have sector_low : 9*q.c < 35*q.s := by linarith only [hD.2.1,tu]
  have sector_high : 37*q.s < 13*q.c := by linarith only [hD.2.2.1,wv]
  have sector_square := mul_nonneg
    (show 0 ≤ 13*q.c-37*q.s by linarith only [sector_high])
    (show 0 ≤ 13*q.c+37*q.s by linarith only [hc,hs])
  have c_lower : 15/16 ≤ q.c := by
    apply le_of_not_gt
    intro small
    have product := mul_nonneg
      (show 0 ≤ 15/16-q.c by linarith only [small])
      (show 0 ≤ 15/16+q.c by linarith only [hc])
    nlinarith only [sector_square,product,q.unit_normal]
  have s_lower : 6/25 ≤ q.s := by linarith only [sector_low,c_lower]
  have product := mul_nonneg
    (show 0 ≤ 13*q.c-37*q.s by linarith only [sector_high])
    (show 0 ≤ 37*q.c-13*q.s by linarith only [sector_high,hc])
  have sum_upper : q.c+q.s ≤ 13/10 := by
    nlinarith only [product,q.unit_normal,sq_nonneg (q.c+q.s-13/10)]
  have half_width : q.side/2*(q.c+q.s) ≤ 69/100 := by
    have bound := mul_le_mul cap sum_upper
      (show 0 ≤ q.c+q.s by linarith only [hc,hs]) (by norm_num : (0:ℝ) ≤ 1001/1000)
    nlinarith only [bound]
  have uweight := mul_nonneg hs (sub_nonneg.mpr hD.2.1.le)
  have vweight := mul_nonneg hc (sub_nonneg.mpr wv)
  have strict := mul_pos (sub_pos.mpr ha)
    (show 0 < q.c-q.s by linarith only [sector_high,c_lower])
  have cs_lower := mul_nonneg hs (sub_nonneg.mpr c_lower)
  have y_lower : 9/4 ≤ centerY q := by
    dsimp [centerY]
    nlinarith only [uweight,vweight,strict,q.unit_normal,
      c_lower,s_lower,cs_lower,sq_nonneg q.s]
  have xD := ThreeSquare.inside_support q (87/50) 2 1 0 hD
  have xQ := ThreeSquare.inside_support q 1 (12/5) 1 0 hQ
  have yP := ThreeSquare.inside_support q (457/500) 2 0 1 hP
  simp only [ThreeSquare.supportRadius,one_mul,zero_mul,add_zero,zero_add,
    neg_mul,neg_zero,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at xD xQ yP
  obtain ⟨xDlo,xDhi⟩ := abs_le.mp xD
  obtain ⟨xQlo,xQhi⟩ := abs_le.mp xQ
  obtain ⟨yPlo,yPhi⟩ := abs_le.mp yP
  exact ⟨by linarith only [xDhi,half_width],
    by linarith only [xQlo,half_width],y_lower,
    by linarith only [yPlo,half_width]⟩

/-- Exact original-center enclosure from five actual point facts, covering
every orientation by face reindexing. The point D is owned, not excluded. -/
theorem center_box (q : OpenSquare)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hD : q.Inside (87/50) 2)
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) :
    21/20 ≤ centerX q ∧ centerX q ≤ 7/4 ∧
      9/4 ≤ centerY q ∧ centerY q ≤ 59/20 := by
  obtain ⟨r,hc,hs,hside,hcx,hcy,hi⟩ := exists_positive_frame q
  have bound := positive_box r (by simpa only [hside] using ha)
    (by simpa only [hside] using cap) hc hs
    ((hi _ _).mpr hP) ((hi _ _).mpr hQ) ((hi _ _).mpr hD)
    (fun hp => hW ((hi _ _).mp hp)) (fun hp => hT ((hi _ _).mp hp))
  simpa only [hcx,hcy] using bound

#print axioms center_box
end N12Compact.WallInwardCenter
