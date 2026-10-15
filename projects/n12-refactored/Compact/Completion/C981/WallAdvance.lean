import Compact.Completion.C981.WallScalars
import S12.Container

/-! Theorem 4 of C981-WALL-CYCLES: an actual wall owner advances to
height 2.8 using the actual singleton seed and central marker exclusions.
The face exclusions are weak and all resulting point bands are strict. -/
namespace N12Compact.C981CompletionWallAdvance

open S12 S12Pilot
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side))
    (marker : q.Inside (457/500) 2) (upper : q.Inside 1 (12/5))
    (lowMissing : ¬ q.Inside 1 (87/50))
    (seedMissing : ¬ q.Inside (19/25) (187/100))
    (centralMissing : ¬ q.Inside (33/20) (47/20)) :
    q.Inside 1 (14/5) := by
  have cone : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have sone : q.s ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.c,sq_nonneg (q.s-1)]
  have product := mul_nonneg hc hs
  have sum : 1 ≤ q.c+q.s := by nlinarith only [q.unit_normal,product,hc,hs]
  have arc := C981CompletionWallScalars.wall_arc q.c q.s hc hs q.unit_normal
  have uLow : q.loU < q.c+q.s*(14/5) := by linarith only [upper.1,hs]
  have vLow : q.loV < -q.s+q.c*(14/5) := by linarith only [upper.2.2.1,hc]
  have fUhi : q.c+q.s*(87/50) < q.loU+q.side := by linarith only [upper.2.1,hs]
  have fVhi : -q.s+q.c*(87/50) < q.loV+q.side := by linarith only [upper.2.2.2,hc]
  have fFaces : q.c+q.s*(87/50) ≤ q.loU ∨
      -q.s+q.c*(87/50) ≤ q.loV := by
    by_cases u : q.c+q.s*(87/50) ≤ q.loU
    · exact Or.inl u
    · exact Or.inr (le_of_not_gt (fun v => lowMissing
        ⟨by simpa only [mul_one] using lt_of_not_ge u,
          by simpa only [mul_one] using fUhi,
          by simpa only [mul_one] using v,
          by simpa only [mul_one] using fVhi⟩))
  have seedUhi : q.c*(19/25)+q.s*(187/100) < q.loU+q.side := by
    linarith only [marker.2.1,hc,hs]
  have centralUlo : q.loU < q.c*(33/20)+q.s*(47/20) := by
    linarith only [marker.1,hc,hs]
  have centralVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
    linarith only [upper.2.2.2,hc,hs]
  have centralFace (uHi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side) :
      -q.s*(33/20)+q.c*(47/20) ≤ q.loV :=
    le_of_not_gt (fun v => centralMissing ⟨centralUlo,uHi,v,centralVhi⟩)
  have seedFaces (vHi : -q.s*(19/25)+q.c*(187/100) < q.loV+q.side) :
      q.c*(19/25)+q.s*(187/100) ≤ q.loU ∨
        -q.s*(19/25)+q.c*(187/100) ≤ q.loV := by
    by_cases u : q.c*(19/25)+q.s*(187/100) ≤ q.loU
    · exact Or.inl u
    · exact Or.inr (le_of_not_gt (fun v => seedMissing
        ⟨lt_of_not_ge u,seedUhi,v,vHi⟩))
  have seedUpperU (bound : -q.s*(19/25)+q.c*(187/100) ≤ q.loV) :
      q.c+q.s*(14/5) < q.loU+q.side := by
    apply lt_of_not_ge
    intro cap
    have lowerProduct := mul_nonneg hs (sub_nonneg.mpr bound)
    have upperProduct := mul_nonneg hc (sub_nonneg.mpr cap)
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [sum])
    nlinarith only [wall,lowerProduct,upperProduct,strict,arc,q.unit_normal]
  have seedLowerU (bound : q.c*(19/25)+q.s*(187/100) ≤ q.loU) :
      q.c+q.s*(14/5) < q.loU+q.side := by
    have short := (short_projections q (6/25) (93/100) (by norm_num)).2.1
    linarith only [bound,short,side]
  have centralUpperV (bound : -q.s*(33/20)+q.c*(47/20) ≤ q.loV) :
      -q.s+q.c*(14/5) < q.loV+q.side := by
    have short := (short_projections q (-(13/20)) (9/20) (by norm_num)).2.2.2
    linarith only [bound,short,side]
  rcases fFaces with fU | fV
  · have centralUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by
      have short := (short_projections q (13/20) (61/100) (by norm_num)).2.1
      linarith only [fU,short,side]
    have mV := centralFace centralUhi
    have seedVhi : -q.s*(19/25)+q.c*(187/100) < q.loV+q.side := by
      linarith only [mV,sone,hc,side]
    have targetUhi : q.c+q.s*(14/5) < q.loU+q.side := by
      rcases seedFaces seedVhi with seedU | seedV
      · exact seedLowerU seedU
      · exact seedUpperU seedV
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [uLow,targetUhi,vLow,centralUpperV mV]
  · have seedVhi : -q.s*(19/25)+q.c*(187/100) < q.loV+q.side := by
      have short := (short_projections q (-(6/25)) (13/100) (by norm_num)).2.2.2
      linarith only [fV,short,side]
    rcases seedFaces seedVhi with seedU | seedV
    · have targetUhi := seedLowerU seedU
      have targetVhi : -q.s+q.c*(14/5) < q.loV+q.side := by
        by_cases shallow : (53/50)*q.c ≤ 1
        · linarith only [fV,shallow,side]
        · have large : 50/53 < q.c := by linarith only [shallow]
          have short := C981CompletionWallScalars.small_projection q.c q.s
            large hs q.unit_normal
          have centralUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by
            linarith only [seedU,short,side]
          exact centralUpperV (centralFace centralUhi)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,targetUhi,vLow,targetVhi]
    · have targetUhi := seedUpperU seedV
      have targetVhi : -q.s+q.c*(14/5) < q.loV+q.side := by
        have short := (short_projections q (6/25) (93/100) (by norm_num)).2.2.2
        linarith only [seedV,short,side]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,targetUhi,vLow,targetVhi]

/-- All orientations of the actual left-wall square, without a side cap. -/
theorem point (q : OpenSquare) (side : 1 < q.side) (box : InsideContainer q)
    (marker : q.Inside (457/500) 2) (upper : q.Inside 1 (12/5))
    (lowMissing : ¬ q.Inside 1 (87/50))
    (seedMissing : ¬ q.Inside (19/25) (187/100))
    (centralMissing : ¬ q.Inside (33/20) (47/20)) :
    q.Inside 1 (14/5) := by
  obtain ⟨r,hc,hs,shape,_,_,equivalent⟩ := exists_positive_frame q
  have rBox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y h
    have bound := box x y ((equivalent _ _).mp h)
    exact ⟨bound.1,bound.2.2.1⟩
  have wall : 0 ≤ r.c*r.loU-r.s*(r.loV+r.side) := by
    have bound := (positive_frame_wall_bounds r hc hs rBox).1
    dsimp [centerX] at bound
    nlinarith only [bound]
  exact (equivalent _ _).mp (positive_point r (by simpa only [shape] using side)
    hc hs wall ((equivalent _ _).mpr marker) ((equivalent _ _).mpr upper)
    (fun h => lowMissing ((equivalent _ _).mp h))
    (fun h => seedMissing ((equivalent _ _).mp h))
    (fun h => centralMissing ((equivalent _ _).mp h)))

#print axioms point
end N12Compact.C981CompletionWallAdvance
