import S12.ShortCluster.Projections
import S12.WallGeometry
import Mathlib.Tactic.LinearCombination

/-! The retained all-angle one-sided central crosspoint lemma, reproduced
in the appendix of C893-CONTINUOUS-EXCLUSION. All four foreign points are
weak absences from the actual square; no center or container is assumed. -/
namespace N12Compact.C981CompletionCrosspoint

open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (north : q.Inside 2 (113/50)) (east : q.Inside (113/50) 2)
    (marker : q.Inside (47/20) (47/20))
    (missingSE : ¬ q.Inside (47/20) (33/20))
    (missingNW : ¬ q.Inside (33/20) (47/20))
    (rightLow : ¬ q.Inside 3 (12/5)) (rightHigh : ¬ q.Inside 3 (5/2)) :
    q.Inside 2 (5/2) := by
  have sone : q.s ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.c,sq_nonneg (q.s-1)]
  have targetUlo : q.loU < 2*q.c+(5/2)*q.s := by linarith only [north.1,hs]
  have targetVlo : q.loV < -2*q.s+(5/2)*q.c := by linarith only [east.2.2.1,hc,hs]
  have gUhi : (47/20)*q.c+(33/20)*q.s < q.loU+q.side := by
    linarith only [marker.2.1,hs]
  have gVhi : -(47/20)*q.s+(33/20)*q.c < q.loV+q.side := by
    linarith only [north.2.2.2,hc,hs]
  have modes : (47/20)*q.c+(33/20)*q.s ≤ q.loU ∨
      -(47/20)*q.s+(33/20)*q.c ≤ q.loV := by
    by_cases lower : (47/20)*q.c+(33/20)*q.s ≤ q.loU
    · exact Or.inl lower
    · right
      apply le_of_not_gt
      intro v
      apply missingSE
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lower,gUhi,v,gVhi]
  have shortTarget := short_projections q (-(7/20)) (17/20) (by norm_num)
  rcases modes with lowerU | lowerV
  · have slope : 35*q.c < 61*q.s := by linarith only [lowerU,north.1]
    have targetUhi : 2*q.c+(5/2)*q.s < q.loU+q.side := by
      linarith only [lowerU,shortTarget.2.1,side]
    have rUlo : q.loU < 3*q.c+(12/5)*q.s := by linarith only [marker.1,hc,hs]
    have rUhi : 3*q.c+(12/5)*q.s < q.loU+q.side := by
      have short := (short_projections q (13/20) (3/4) (by norm_num)).2.1
      linarith only [lowerU,short,side]
    have rVhi : -3*q.s+(12/5)*q.c < q.loV+q.side := by
      linarith only [north.2.2.2,slope,hc,hs]
    have rFace : -3*q.s+(12/5)*q.c ≤ q.loV := by
      apply le_of_not_gt
      intro v
      apply rightLow
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rUlo,rUhi,v,rVhi]
    have targetVhi : -2*q.s+(5/2)*q.c < q.loV+q.side := by
      by_cases moderate : 20*q.s ≤ 99*q.c
      · have product := mul_nonpos_of_nonneg_of_nonpos hc
          (show 20*q.s-99*q.c ≤ 0 by linarith only [moderate])
        have identity : (q.s+q.c/10)^2-1=(q.c/100)*(20*q.s-99*q.c) := by
          linear_combination q.unit_normal
        have bound : q.s+q.c/10 ≤ 1 := by
          nlinarith only [identity,product,sq_nonneg (q.s+q.c/10-1)]
        linarith only [rFace,bound,side]
      · have large : 99*q.c < 20*q.s := lt_of_not_ge moderate
        have r1Ulo : q.loU < 3*q.c+(5/2)*q.s := by linarith only [marker.1,hc,hs]
        have r1Uhi : 3*q.c+(5/2)*q.s < q.loU+q.side := by
          linarith only [lowerU,large,sone,side]
        have r1Vhi : -3*q.s+(5/2)*q.c < q.loV+q.side := by
          linarith only [north.2.2.2,slope,hc,hs]
        have r1Face : -3*q.s+(5/2)*q.c ≤ q.loV := by
          apply le_of_not_gt
          intro v
          apply rightHigh
          refine ⟨?_,?_,?_,?_⟩ <;> linarith only [r1Ulo,r1Uhi,v,r1Vhi]
        linarith only [r1Face,sone,side]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [targetUlo,targetUhi,targetVlo,targetVhi]
  · have bUhi : (33/20)*q.c+(47/20)*q.s < q.loU+q.side := by
      linarith only [marker.2.1,hc]
    have bVlo : q.loV < -(33/20)*q.s+(47/20)*q.c := by
      linarith only [east.2.2.1,hc,hs]
    have bVhi : -(33/20)*q.s+(47/20)*q.c < q.loV+q.side := by
      have short := (short_projections q (-(7/10)) (7/10) (by norm_num)).2.2.2
      linarith only [lowerV,short,side]
    have bFace : (33/20)*q.c+(47/20)*q.s ≤ q.loU := by
      apply le_of_not_gt
      intro u
      apply missingNW
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [u,bUhi,bVlo,bVhi]
    have short := (short_projections q (7/20) (3/20) (by norm_num)).2.1
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [targetUlo,targetVlo,bFace,short,lowerV,shortTarget.2.2.2,side]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (north : q.Inside 2 (113/50)) (east : q.Inside (113/50) 2)
    (marker : q.Inside (47/20) (47/20))
    (missingSE : ¬ q.Inside (47/20) (33/20))
    (missingNW : ¬ q.Inside (33/20) (47/20))
    (rightLow : ¬ q.Inside 3 (12/5)) (rightHigh : ¬ q.Inside 3 (5/2)) :
    q.Inside 2 (5/2) := by
  obtain ⟨r,hc,hs,shape,_,_,equivalent⟩ := exists_positive_frame q
  exact (equivalent _ _).mp (positive r (by simpa only [shape] using side) hc hs
    ((equivalent _ _).mpr north) ((equivalent _ _).mpr east) ((equivalent _ _).mpr marker)
    (fun h => missingSE ((equivalent _ _).mp h))
    (fun h => missingNW ((equivalent _ _).mp h))
    (fun h => rightLow ((equivalent _ _).mp h))
    (fun h => rightHigh ((equivalent _ _).mp h)))

#print axioms point
end N12Compact.C981CompletionCrosspoint
