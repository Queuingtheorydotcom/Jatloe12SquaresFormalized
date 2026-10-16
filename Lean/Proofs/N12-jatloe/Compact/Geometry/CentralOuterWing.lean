import S12.WallGeometry
import S12.ShortCluster

/-! An inward central point forces the adjacent outer wing point. The
foreign point is the actual southwest central crosspoint, not a proposed
center or a saved pose bound. Four face combinations suffice uniformly
over every orientation, and no container or upper side bound is used. -/
namespace N12Compact.CentralOuterWing
open S12 S12Pilot
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (size : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (p : q.Inside (33/20) (47/20))
    (d : q.Inside 2 (113/50))
    (w : q.Inside (87/50) 3)
    (missing : ¬ q.Inside (47/20) (47/20))
    (foreign : ¬ q.Inside (3/2) 2) : q.Inside (8/5) 3 := by
  have cmax : q.c ≤ 1 := by
    nlinarith only [q.unit_normal, sq_nonneg q.s, hc]
  have fUhi : q.c*(8/5)+q.s*3 < q.loU+q.side := by
    linarith only [w.2.1,hc]
  have fVlo : q.loV < -q.s*(8/5)+q.c*3 := by
    linarith only [p.2.2.1,hc,hs]
  have tUlo : q.loU < q.c*(47/20)+q.s*(47/20) := by
    linarith only [p.1,hc]
  have tVhi : -q.s*(47/20)+q.c*(47/20) < q.loV+q.side := by
    linarith only [p.2.2.2,hs]
  have tFaces : q.loU+q.side ≤ q.c*(47/20)+q.s*(47/20) ∨
      -q.s*(47/20)+q.c*(47/20) ≤ q.loV := by
    by_cases h : q.loU+q.side ≤ q.c*(47/20)+q.s*(47/20)
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt (fun hv =>
        missing ⟨tUlo,lt_of_not_ge h,hv,tVhi⟩))
  by_contra notF
  have fFaces : q.c*(8/5)+q.s*3 ≤ q.loU ∨
      q.loV+q.side ≤ -q.s*(8/5)+q.c*3 := by
    by_cases h : q.c*(8/5)+q.s*3 ≤ q.loU
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt (fun hv =>
        notF ⟨lt_of_not_ge h,fUhi,fVlo,hv⟩))
  rcases fFaces with fU | fV
  · rcases tFaces with tU | tV
    · linarith only [fU,tU,size,cmax,hs]
    · linarith only [fU,p.1,tV,d.2.2.1,hc,hs]
  · rcases tFaces with tU | tV
    · have widthU := (short_projections q (17/20) (7/20) (by norm_num)).2.1
      have zUlo : q.loU < q.c*(3/2)+q.s*2 := by
        linarith only [tU,size,widthU]
      have zUhi : q.c*(3/2)+q.s*2 < q.loU+q.side := by
        linarith only [w.2.1,hc,hs]
      have zVlo : q.loV < -q.s*(3/2)+q.c*2 := by
        linarith only [fV,size,cmax,hs]
      have angle : 65*q.s < 61*q.c := by
        linarith only [w.2.1,tU]
      have zVhi : -q.s*(3/2)+q.c*2 < q.loV+q.side := by
        linarith only [w.2.2.2,angle,hc,hs]
      exact foreign ⟨zUlo,zUhi,zVlo,zVhi⟩
    · have widthV := (short_projections q (13/20) (3/4) (by norm_num)).2.1
      linarith only [fV,tV,size,widthV]

/-- The northwest central square reaches `(1.6,3)` whenever it owns the
inward point `(2,2.26)`. The southwest central square's genuine crosspoint
`(1.5,2)` provides the only foreign-point premise. -/
theorem point (q : OpenSquare) (size : 1 < q.side)
    (p : q.Inside (33/20) (47/20))
    (d : q.Inside 2 (113/50))
    (w : q.Inside (87/50) 3)
    (missing : ¬ q.Inside (47/20) (47/20))
    (foreign : ¬ q.Inside (3/2) 2) : q.Inside (8/5) 3 := by
  obtain ⟨r,hc,hs,same,_,_,inside⟩ := exists_positive_frame q
  exact (inside _ _).mp (positive_point r (by simpa only [same] using size)
    hc hs ((inside _ _).mpr p) ((inside _ _).mpr d) ((inside _ _).mpr w)
    (fun h => missing ((inside _ _).mp h))
    (fun h => foreign ((inside _ _).mp h)))

#print axioms point
end N12Compact.CentralOuterWing
