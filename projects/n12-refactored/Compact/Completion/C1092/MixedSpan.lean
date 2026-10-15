import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The full six-point mixed-span obstruction in the original coordinate
chart. Both signed canonical orientations, zero and contact are included.
The two continuous scalar bounds use quadratic nonnegative factors. -/
namespace N12Compact.C1092MixedSpan
open S12 S12Pilot
set_option Elab.async false

private theorem canonical_impossible (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (range : |q.s| ≤ q.c)
    (A : q.Inside 2 (87/50)) (B : q.Inside 3 (8/5))
    (D : ¬ q.Inside (113/50) 2) (H : ¬ q.Inside 3 (87/50))
    (F : ¬ q.Inside (113/50) 1) (T : ¬ q.Inside (12/5) 1) : False := by
  classical
  have bounds := abs_le.mp range
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,hc]
  by_cases sign : q.s ≤ 0
  · have du0 : q.loU < q.c*(113/50)+q.s*2 := by
      linarith only [A.1,hc,bounds.1]
    have du1 : q.c*(113/50)+q.s*2 < q.loU+q.side := by
      linarith only [B.2.1,hc,sign]
    have dv0 : q.loV < -q.s*(113/50)+q.c*2 := by
      linarith only [A.2.2.1,hc,sign]
    have dv1 : q.loV+q.side ≤ -q.s*(113/50)+q.c*2 :=
      le_of_not_gt (fun h => D ⟨du0,du1,dv0,h⟩)
    have fu0 : q.loU < q.c*(113/50)+q.s := by
      linarith only [A.1,hc,sign]
    have fu1 : q.c*(113/50)+q.s < q.loU+q.side := by
      linarith only [B.2.1,hc,bounds.1]
    have fv1 : -q.s*(113/50)+q.c < q.loV+q.side := by
      linarith only [A.2.2.2,hc,bounds.1]
    have fv0 : -q.s*(113/50)+q.c ≤ q.loV := by
      apply le_of_not_gt
      intro h
      apply F
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro fu0 (And.intro fu1 (And.intro h fv1))
    linarith only [dv1,fv0,ha,cu]
  · have sn : 0 ≤ q.s := (lt_of_not_ge sign).le
    have hu0 : q.loU < q.c*3+q.s*(87/50) := by
      linarith only [B.1,sn]
    have hv0 : q.loV < -q.s*3+q.c*(87/50) := by
      linarith only [B.2.2.1,hc]
    have hv1 : -q.s*3+q.c*(87/50) < q.loV+q.side := by
      linarith only [A.2.2.2,sn]
    have hu1 : q.loU+q.side ≤ q.c*3+q.s*(87/50) :=
      le_of_not_gt (fun h => H ⟨hu0,h,hv0,hv1⟩)
    have du0 : q.loU < q.c*(113/50)+q.s*2 := by
      linarith only [A.1,hc,sn]
    have du1 : q.c*(113/50)+q.s*2 < q.loU+q.side := by
      linarith only [B.2.1,hc,bounds.2]
    have dv0 : q.loV < -q.s*(113/50)+q.c*2 := by
      linarith only [A.2.2.1,bounds.2]
    have dv1 : q.loV+q.side ≤ -q.s*(113/50)+q.c*2 :=
      le_of_not_gt (fun h => D ⟨du0,du1,dv0,h⟩)
    have fu1 : q.c*(113/50)+q.s < q.loU+q.side := by
      linarith only [B.2.1,hc,sn]
    have fv1 : -q.s*(113/50)+q.c < q.loV+q.side := by
      linarith only [A.2.2.2,hc,sn]
    have fv0 : q.loV < -q.s*(113/50)+q.c := by
      by_contra bad
      have missingV : -q.s*(113/50)+q.c ≤ q.loV := le_of_not_gt bad
      linarith only [dv1,missingV,ha,cu]
    have fu0 : q.c*(113/50)+q.s ≤ q.loU := by
      apply le_of_not_gt
      intro h
      apply F
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro h (And.intro fu1 (And.intro fv0 fv1))
    have span : q.side ≤ (37/50)*(q.c+q.s) := by linarith only [fu0,hu1]
    have steep : q.c < 2*q.s := by
      by_contra bad
      have low : 2*q.s ≤ q.c := le_of_not_gt bad
      have product := mul_nonneg (sub_nonneg.mpr low)
        (show 0 ≤ 2*q.c-q.s by linarith only [hc,bounds.2])
      have short : ((37/50)*(q.c+q.s))^2 ≤ 61605/62500 := by
        nlinarith only [product,q.unit_normal]
      have large : 1 < (37/50)*(q.c+q.s) := lt_of_lt_of_le ha span
      have contradiction := mul_pos (sub_pos.mpr large)
        (show 0 < (37/50)*(q.c+q.s)+1 by linarith only [large])
      nlinarith only [short,contradiction]
    have tu1 : q.c*(12/5)+q.s < q.loU+q.side := by
      linarith only [B.2.1,hc,sn]
    have tv1 : -q.s*(12/5)+q.c < q.loV+q.side := by
      linarith only [A.2.2.2,hc,sn]
    have tu0 : q.loU < q.c*(12/5)+q.s := by
      by_contra bad
      have face : q.c*(12/5)+q.s ≤ q.loU := le_of_not_gt bad
      have short := short_projections q (3-12/5) (87/50-1) (by norm_num)
      linarith only [face,hu1,ha,short.2.1]
    have tv0 : -q.s*(12/5)+q.c ≤ q.loV := by
      apply le_of_not_gt
      intro h
      apply T
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro tu0 (And.intro tu1 (And.intro h tv1))
    have finalSpan : q.side ≤ q.c+(7/50)*q.s := by linarith only [dv1,tv0]
    have product := mul_nonneg sn
      (show 0 ≤ (2451/2500)*q.s-(7/25)*q.c by linarith only [steep,sn])
    have short : (q.c+(7/50)*q.s)^2 ≤ 1 := by nlinarith only [product,q.unit_normal]
    have large : 1 < q.c+(7/50)*q.s := lt_of_lt_of_le ha finalSpan
    have contradiction := mul_pos (sub_pos.mpr large)
      (show 0 < q.c+(7/50)*q.s+1 by linarith only [large])
    nlinarith only [short,contradiction]

theorem impossible (q : OpenSquare) (ha : 1 < q.side)
    (A : q.Inside 2 (87/50)) (B : q.Inside 3 (8/5))
    (D : ¬ q.Inside (113/50) 2) (H : ¬ q.Inside 3 (87/50))
    (F : ¬ q.Inside (113/50) 1) (T : ¬ q.Inside (12/5) 1) : False := by
  obtain ⟨r,hc,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  exact canonical_impossible r (by simpa only [side] using ha) hc range
    ((inside _ _).mpr A) ((inside _ _).mpr B)
    (fun h => D ((inside _ _).mp h)) (fun h => H ((inside _ _).mp h))
    (fun h => F ((inside _ _).mp h)) (fun h => T ((inside _ _).mp h))

#print axioms impossible
end N12Compact.C1092MixedSpan
