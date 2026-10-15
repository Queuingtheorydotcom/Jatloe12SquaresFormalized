import S12.ShortCluster.Projections
import Compact.Geometry.ClosedFrames

/-! The paired-corner advancement needed by the common C981 entrance.
This is the exact (p,q,r)=(.74,.2,.6) instance of OTHER-GEOMETRY Theorem5.
A positive-quadrant face reindexing suffices; its components need no order. -/
namespace N12Compact.C981CompletionCornerAdvance

open S12 S12Pilot
set_option Elab.async false

theorem upper_wall (q : OpenSquare)
    (wall : ∀ x y, q.Inside x y → y ≤ 1) :
    q.s*(q.loU+q.side)+q.c*(q.loV+q.side) ≤ 1 := by
  have limit : 0 ≤ 1-(q.s*(q.loU+q.side)+q.c*(q.loV+q.side)) := by
    apply affine_endpoint_nonnegative q.side (q.c+q.s) _ q.side_pos
    intro t positive small
    let u := q.loU+q.side-t
    let v := q.loV+q.side-t
    have point : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
      apply (inside_iff_rotated_box q _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := wall _ _ point
    dsimp [u,v] at bound
    nlinarith only [bound]
  linarith only [limit]

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s)
    (wall : q.s*(q.loU+q.side)+q.c*(q.loV+q.side) ≤ 1)
    (origin : q.Inside 0 0) (missingLeft : ¬ q.Inside (-(1/5)) 0)
    (missingBelow : ¬ q.Inside 0 (-(37/50))) : q.Inside (3/5) 0 := by
  have cone : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have sone : q.s ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.c,sq_nonneg (q.s-1)]
  have cross := mul_nonneg hc.le hs
  have sum : 1 ≤ q.c+q.s := by nlinarith only [q.unit_normal,cross,hc,hs]
  have sumHigh : q.c+q.s ≤ 10/7 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),hc,hs]
  have arc : 1+(4/5)*q.c*q.s ≤ q.c+q.s := by
    have product := mul_nonneg (sub_nonneg.mpr sum) (sub_nonneg.mpr sumHigh)
    nlinarith only [product,q.unit_normal,cross]
  have fUhi : -q.c/5 < q.loU+q.side := by linarith only [origin.2.1,hc]
  have fVlo : q.loV < q.s/5 := by linarith only [origin.2.2.1,hs]
  have modes : -q.c/5 ≤ q.loU ∨ q.loV+q.side ≤ q.s/5 := by
    by_cases first : -q.c/5 ≤ q.loU
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro v
      apply missingLeft
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [first,fUhi,fVlo,v]
  have uLow : q.loU < (3/5)*q.c := by linarith only [origin.1,hc]
  have vHigh : -(3/5)*q.s < q.loV+q.side := by linarith only [origin.2.2.2,hs]
  rcases modes with fU | fV
  · have uHigh : (3/5)*q.c < q.loU+q.side := by linarith only [fU,side,cone]
    have vLow : q.loV < -(3/5)*q.s := by
      apply lt_of_not_ge
      intro low
      have first := mul_nonneg hs (sub_nonneg.mpr fU)
      have last := mul_nonneg hc.le (show 0 ≤ q.loV+(3/5)*q.s by linarith only [low])
      have strict := mul_pos (sub_pos.mpr side) (show 0 < q.c+q.s by linarith only [sum])
      nlinarith only [first,last,strict,wall,arc]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]
  · have vLow : q.loV < -(3/5)*q.s := by linarith only [fV,side,sone]
    have hUhi : -(37/50)*q.s < q.loU+q.side := by linarith only [origin.2.1,hs]
    have hVhi : -(37/50)*q.c < q.loV+q.side := by linarith only [origin.2.2.2,hc]
    have hVlo : q.loV < -(37/50)*q.c := by
      have short := (short_projections q (37/50) (1/5) (by norm_num)).2.1
      linarith only [fV,short,side]
    have hFace : -(37/50)*q.s ≤ q.loU := by
      apply le_of_not_gt
      intro u
      apply missingBelow
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [u,hUhi,hVlo,hVhi]
    have short := (short_projections q (3/5) (37/50) (by norm_num)).2.1
    have uHigh : (3/5)*q.c < q.loU+q.side := by linarith only [hFace,short,side]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

/-- Actual upper coordinate wall; no side cap or other wall is required. -/
theorem point (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → y ≤ 1)
    (origin : q.Inside 0 0) (missingLeft : ¬ q.Inside (-(1/5)) 0)
    (missingBelow : ¬ q.Inside 0 (-(37/50))) : q.Inside (3/5) 0 := by
  obtain ⟨r,hc,hs,shape,equivalent,_⟩ := ClosedFrames.positive_frame q
  have rWall : ∀ x y, r.Inside x y → y ≤ 1 := fun x y h => wall x y ((equivalent _ _).mp h)
  exact (equivalent _ _).mp (positive r (by simpa only [shape] using side) hc hs
    (upper_wall r rWall) ((equivalent _ _).mpr origin)
    (fun h => missingLeft ((equivalent _ _).mp h))
    (fun h => missingBelow ((equivalent _ _).mp h)))

#print axioms point
end N12Compact.C981CompletionCornerAdvance
