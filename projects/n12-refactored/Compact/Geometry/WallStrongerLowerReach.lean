import Compact.Geometry.WallLowerReach

/-! A stronger actual neighboring exclusion advances the wall reach to
2.6. The inward exclusion is supplied by the central crosspoint; the
lower exclusion is the strengthened missing-corner singleton point. -/
namespace N12Compact.WallStrongerLowerReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (ha : 1<q.side)
    (hc : 0≤q.c) (hs : 0≤q.s)
    (wall : 0≤q.c*q.loU-q.s*(q.loV+q.side))
    (marker : q.Inside (457/500) 2) (high : q.Inside 1 (12/5))
    (missingLow : ¬q.Inside 1 (91/50))
    (missingInward : ¬q.Inside (3/2) 2) : q.Inside 1 (13/5) := by
  have product : 0≤q.c*q.s := mul_nonneg hc hs
  have sum : 1≤q.c+q.s := by
    nlinarith only [q.unit_normal,product,hc,hs]
  have sumHi : q.c+q.s≤10/7 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),hc,hs]
  have arc : 1+(41/50)*q.c*q.s≤q.c+q.s := by
    nlinarith only [q.unit_normal,product,
      mul_nonneg (sub_nonneg.mpr sumHi) (sub_nonneg.mpr sum)]
  have targetUlo : q.loU<q.c+(13/5)*q.s := by
    nlinarith only [marker.1,hc,hs]
  have targetVlo : q.loV< -q.s+(13/5)*q.c := by
    nlinarith only [high.2.2.1,hc]
  have inwardUlo : q.loU<(3/2)*q.c+2*q.s := by
    nlinarith only [marker.1,hc]
  have inwardVhi : -(3/2)*q.s+2*q.c<q.loV+q.side := by
    nlinarith only [high.2.2.2,hc,hs]
  have inwardFaces : q.loU+q.side≤(3/2)*q.c+2*q.s ∨
      -(3/2)*q.s+2*q.c≤q.loV := by
    by_cases face : q.loU+q.side≤(3/2)*q.c+2*q.s
    · exact Or.inl face
    · right
      apply le_of_not_gt
      intro low
      apply missingInward
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [inwardUlo,face,low,inwardVhi]
  have lowUhi : q.c+(91/50)*q.s<q.loU+q.side := by
    nlinarith only [high.2.1,hs]
  have lowVhi : -q.s+(91/50)*q.c<q.loV+q.side := by
    nlinarith only [marker.2.2.2,hc,hs]
  have lowFaces : q.c+(91/50)*q.s≤q.loU ∨
      -q.s+(91/50)*q.c≤q.loV := by
    by_cases face : q.c+(91/50)*q.s≤q.loU
    · exact Or.inl face
    · right
      apply le_of_not_gt
      intro low
      apply missingLow
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [face,lowUhi,low,lowVhi]
  have lowWidth := short_projections q 0 (39/50) (by norm_num)
  rcases lowFaces with lowerU | lowerV
  · have short := (short_projections q (1/2) (9/50) (by norm_num)).2.1
    have inwardLower : -(3/2)*q.s+2*q.c≤q.loV := by
      rcases inwardFaces with upperU | lowerV
      · exfalso
        linarith only [lowerU,upperU,short,ha]
      · exact lowerV
    have diagonal := (short_projections q (-(1/2)) (3/5) (by norm_num)).2.2.2
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [targetUlo,targetVlo,lowerU,inwardLower,
        lowWidth.2.1,diagonal,ha]
  · have lowerProduct := mul_nonneg hs (sub_nonneg.mpr lowerV)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0<q.c+q.s by linarith only [sum])
    have targetUhi : q.c+(13/5)*q.s<q.loU+q.side := by
      apply lt_of_not_ge
      intro cap
      have upperProduct := mul_nonneg hc (sub_nonneg.mpr cap)
      nlinarith only [wall,lowerProduct,strict,upperProduct,arc,q.unit_normal,product]
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [targetUlo,targetUhi,targetVlo,lowerV,lowWidth.2.2.2,ha]

/-- Both signs and all face reindexings of the actual wall are covered. -/
theorem point (q : OpenSquare) (ha : 1<q.side) (box : InsideContainer q)
    (marker : q.Inside (457/500) 2) (high : q.Inside 1 (12/5))
    (missingLow : ¬q.Inside 1 (91/50))
    (missingInward : ¬q.Inside (3/2) 2) : q.Inside 1 (13/5) := by
  obtain ⟨r,hc,hs,shape,_,_,equivalent⟩ := exists_positive_frame q
  have rBox : ∀ x y, r.Inside x y→0≤x ∧ 0≤y := by
    intro x y point
    have bound := box x y ((equivalent x y).mp point)
    exact ⟨bound.1,bound.2.2.1⟩
  have wall : 0≤r.c*r.loU-r.s*(r.loV+r.side) := by
    have boundary := (positive_frame_wall_bounds r hc hs rBox).1
    dsimp [centerX] at boundary
    nlinarith only [boundary]
  exact (equivalent _ _).mp (positive_point r (by simpa only [shape] using ha)
    hc hs wall ((equivalent _ _).mpr marker) ((equivalent _ _).mpr high)
    (fun h => missingLow ((equivalent _ _).mp h))
    (fun h => missingInward ((equivalent _ _).mp h)))

end N12Compact.WallStrongerLowerReach
