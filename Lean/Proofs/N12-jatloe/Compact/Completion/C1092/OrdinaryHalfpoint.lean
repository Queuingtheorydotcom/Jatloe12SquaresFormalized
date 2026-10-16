import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The all-angle ordinary right-hand central halfpoint theorem. All four
exclusions are genuine point absences; neither a wall nor a side cap is
needed. Contacts and both canonical orientation endpoints are retained. -/
namespace N12Compact.C1092OrdinaryHalfpoint
open S12 S12Pilot
set_option Elab.async false

private theorem canonical (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (range : |q.s| ≤ q.c)
    (marker : q.Inside (47/20) (33/20))
    (A : q.Inside 3 (87/50)) (B : q.Inside 3 (8/5))
    (D : ¬ q.Inside (113/50) 2) (R : ¬ q.Inside 3 2)
    (K : ¬ q.Inside 3 1) (F : ¬ q.Inside (113/50) 1) :
    q.Inside 3 (3/2) := by
  classical
  have bounds := abs_le.mp range
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,hc]
  by_cases sign : 0 ≤ q.s
  · have ku0 : q.loU < q.c*3+q.s := by linarith only [marker.1,bounds.2]
    have ku1 : q.c*3+q.s < q.loU+q.side := by linarith only [B.2.1,sign]
    have kv1 : -q.s*3+q.c < q.loV+q.side := by linarith only [B.2.2.2,hc]
    have kv0 : -q.s*3+q.c ≤ q.loV := by
      apply le_of_not_gt
      intro h
      apply K
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro ku0 (And.intro ku1 (And.intro h kv1))
    have ru0 : q.loU < q.c*3+q.s*2 := by linarith only [marker.1,hc,sign]
    have rv0 : q.loV < -q.s*3+q.c*2 := by linarith only [B.2.2.1,hc]
    have rv1 : -q.s*3+q.c*2 < q.loV+q.side := by linarith only [kv0,ha,cu]
    have ru1 : q.loU+q.side ≤ q.c*3+q.s*2 :=
      le_of_not_gt (fun h => R ⟨ru0,h,rv0,rv1⟩)
    have du0 : q.loU < q.c*(113/50)+q.s*2 := by linarith only [ru1,ha,cu]
    have du1 : q.c*(113/50)+q.s*2 < q.loU+q.side := by
      linarith only [A.2.1,hc,bounds.2]
    have dv0 : q.loV < -q.s*(113/50)+q.c*2 := by linarith only [marker.2.2.1,hc,sign]
    have dv1 : q.loV+q.side ≤ -q.s*(113/50)+q.c*2 :=
      le_of_not_gt (fun h => D ⟨du0,du1,dv0,h⟩)
    have short := short_projections q (113/50-3) (2-3/2) (by norm_num)
    exact ⟨by linarith only [marker.1,hc,bounds.2],
      by linarith only [B.2.1,sign],
      by linarith only [dv1,ha,short.2.2.2],
      by linarith only [B.2.2.2,hc]⟩
  · have sn : q.s ≤ 0 := (lt_of_not_ge sign).le
    have ru0 : q.loU < q.c*3+q.s*2 := by linarith only [marker.1,hc,bounds.1]
    have ru1 : q.c*3+q.s*2 < q.loU+q.side := by linarith only [B.2.1,sn]
    have rv0 : q.loV < -q.s*3+q.c*2 := by linarith only [B.2.2.1,hc]
    have rv1 : q.loV+q.side ≤ -q.s*3+q.c*2 :=
      le_of_not_gt (fun h => R ⟨ru0,ru1,rv0,h⟩)
    have ku0 : q.loU < q.c*3+q.s := by linarith only [marker.1,hc,sn]
    have kv1 : -q.s*3+q.c < q.loV+q.side := by linarith only [marker.2.2.2,bounds.1]
    have kv0 : q.loV < -q.s*3+q.c := by
      by_contra bad
      have low : -q.s*3+q.c ≤ q.loV := le_of_not_gt bad
      linarith only [rv1,low,ha,cu]
    have ku1 : q.loU+q.side ≤ q.c*3+q.s := by
      apply le_of_not_gt
      intro h
      apply K
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro ku0 (And.intro h (And.intro kv0 kv1))
    have yu0 : q.loU < q.c*3+q.s*(3/2) := by linarith only [marker.1,hc,sn]
    have yv0 : q.loV < -q.s*3+q.c*(3/2) := by linarith only [rv1,ha,cu]
    have yv1 : -q.s*3+q.c*(3/2) < q.loV+q.side := by linarith only [B.2.2.2,hc]
    have yu1 : q.c*3+q.s*(3/2) < q.loU+q.side := by
      by_contra bad
      have yu : q.loU+q.side ≤ q.c*3+q.s*(3/2) := le_of_not_gt bad
      have short := short_projections q (3-113/50) (3/2-2) (by norm_num)
      have du0 : q.loU < q.c*(113/50)+q.s*2 := by linarith only [yu,ha,short.2.1]
      have du1 : q.c*(113/50)+q.s*2 < q.loU+q.side := by linarith only [marker.2.1,hc,sn]
      have dv0 : q.loV < -q.s*(113/50)+q.c*2 := by linarith only [marker.2.2.1,hc,bounds.1]
      have dv1 : q.loV+q.side ≤ -q.s*(113/50)+q.c*2 :=
        le_of_not_gt (fun h => D ⟨du0,du1,dv0,h⟩)
      have fv0 : q.loV < -q.s*(113/50)+q.c := by linarith only [dv1,ha,cu]
      have fv1 : -q.s*(113/50)+q.c < q.loV+q.side := by linarith only [marker.2.2.2,hc,sn]
      have fu0 : q.loU < q.c*(113/50)+q.s := by
        by_contra bad
        have face : q.c*(113/50)+q.s ≤ q.loU := le_of_not_gt bad
        linarith only [face,ku1,ha,cu]
      have fu1 : q.loU+q.side ≤ q.c*(113/50)+q.s := by
        apply le_of_not_gt
        intro h
        apply F
        simpa only [OpenSquare.Inside,InBands,mul_one] using
          And.intro fu0 (And.intro h (And.intro fv0 fv1))
      linarith only [B.2.1,fu1,hc,bounds.1]
    exact ⟨yu0,yu1,yv0,yv1⟩

theorem point (q : OpenSquare) (ha : 1 < q.side)
    (marker : q.Inside (47/20) (33/20))
    (A : q.Inside 3 (87/50)) (B : q.Inside 3 (8/5))
    (D : ¬ q.Inside (113/50) 2) (R : ¬ q.Inside 3 2)
    (K : ¬ q.Inside 3 1) (F : ¬ q.Inside (113/50) 1) :
    q.Inside 3 (3/2) := by
  obtain ⟨r,hc,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have h := canonical r (by simpa only [side] using ha) hc range
    ((inside _ _).mpr marker) ((inside _ _).mpr A) ((inside _ _).mpr B)
    (fun h => D ((inside _ _).mp h)) (fun h => R ((inside _ _).mp h))
    (fun h => K ((inside _ _).mp h)) (fun h => F ((inside _ _).mp h))
  exact (inside _ _).mp h

#print axioms point
end N12Compact.C1092OrdinaryHalfpoint
