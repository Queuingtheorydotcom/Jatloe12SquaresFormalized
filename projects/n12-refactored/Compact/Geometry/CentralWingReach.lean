import Compact.Geometry.ClosedFrames
import Compact.Geometry.CentralSegmentAngle
import S12.ShortCluster

/-! An actual foreign segment and a missing central marker force a central
wing square to reach the next boundary point. All angles are covered by
face reindexing; no pose enclosure or numerical certificate is assumed. -/
namespace N12Compact.CentralWingReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem steep_impossible (Q : OpenSquare)
    (hc : 0 < Q.c) (hs : 0 ≤ Q.s) (hsc : Q.s ≤ Q.c)
    (hsteep : Q.c/2 ≤ Q.s) (cap : Q.side ≤ 1001/1000)
    (d : Q.Inside 2 (113/50)) (w : Q.Inside 1 (87/50)) : False := by
  have order := mul_nonneg (sub_nonneg.mpr hsc)
    (show 0 ≤ Q.c+Q.s by linarith only [hc,hs])
  have cmin : 7/10 ≤ Q.c := by
    nlinarith only [Q.unit_normal,order,hc]
  have sector := mul_nonneg
    (show 0 ≤ 2*Q.s-Q.c by linarith only [hsteep])
    (show 0 ≤ 2*Q.c-Q.s by linarith only [hsc,hc])
  have sum : 4/3 ≤ Q.c+Q.s := by
    nlinarith only [Q.unit_normal,sector,hc,hs]
  -- The required U-span is at least 386/375 > 1001/1000.
  linarith only [d.2.1,w.1,cap,cmin,sum]

private theorem negative_point (Q : OpenSquare)
    (ha : 1 < Q.side) (hc : 0 < Q.c) (hs : Q.s < 0)
    (hsc : -Q.c ≤ Q.s)
    (p : Q.Inside (33/20) (33/20))
    (d : Q.Inside 2 (113/50))
    (w : Q.Inside 1 (87/50))
    (t : ¬ Q.Inside (33/20) (47/20)) : Q.Inside 1 (3/2) := by
  have tUlo : Q.loU < Q.c*(33/20)+Q.s*(47/20) := by
    linarith only [w.1,hc,hsc]
  have tUhi : Q.c*(33/20)+Q.s*(47/20) < Q.loU+Q.side := by
    linarith only [d.2.1,hc,hs]
  have tVlo : Q.loV < -Q.s*(33/20)+Q.c*(47/20) := by
    linarith only [p.2.2.1,hc]
  have tVhi : Q.loV+Q.side ≤ -Q.s*(33/20)+Q.c*(47/20) :=
    le_of_not_gt (fun h => t ⟨tUlo,tUhi,tVlo,h⟩)
  have sector : 0 ≤ 9*Q.c+35*Q.s := by
    linarith only [tVhi,d.2.2.2]
  have sectorProduct := mul_nonneg hc.le sector
  have projectedNorm : ((17/20)*Q.c-(13/20)*Q.s)^2 ≤ 1 := by
    -- 400(1-projection²) = 12c(9c+35s)+(c+11s)²+2c²+110s².
    nlinarith only [Q.unit_normal,sectorProduct,
      sq_nonneg (Q.c+11*Q.s),sq_nonneg Q.c,sq_nonneg Q.s]
  have gap : -Q.s*(13/20)+Q.c*(17/20) ≤ 1 := by
    nlinarith only [projectedNorm]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [w.1,hs]
  · linarith only [p.2.1,hc,hsc]
  · linarith only [tVhi,gap,ha]
  · linarith only [w.2.2.2,hc]

/-- Joint point propagation from original strict ownership and disjointness.
The foreign square contributes a closed segment, so contact is permitted.
The conclusion remains strict because the wing's side is greater than one. -/
theorem point_low (Q A : OpenSquare) (ha : 1 < Q.side)
    (cap : Q.side ≤ 1001/1000)
    (p : Q.Inside (33/20) (33/20))
    (d : Q.Inside 2 (113/50))
    (w : Q.Inside 1 (87/50))
    (t : ¬ Q.Inside (33/20) (47/20))
    (e : ClosedInside A 2 (87/50))
    (m : ClosedInside A (113/50) 2)
    (apart : ∀ x y, ¬ (Q.Inside x y ∧ A.Inside x y)) :
    Q.Inside 1 (3/2) := by
  obtain ⟨r,hc,hsc,haeq,hi,_⟩ := ClosedFrames.canonical_frame Q
  have rp := (hi _ _).mpr p
  have rd := (hi _ _).mpr d
  have hW := (hi _ _).mpr w
  have rcap : r.side ≤ 1001/1000 := by simpa only [haeq] using cap
  have rs : r.s < 0 := by
    by_contra h
    have hs : 0 ≤ r.s := le_of_not_gt h
    by_cases hsmall : r.s ≤ r.c/2
    · apply CentralSegmentAngle.exclude_small_nonnegative r A hc hs hsmall rp rd e m
      intro x y hxy
      exact apart x y ⟨(hi x y).mp hxy.1,hxy.2⟩
    · exact steep_impossible r hc hs (abs_le.mp hsc).2
        (lt_of_not_ge hsmall).le rcap rd hW
  exact (hi _ _).mp (negative_point r (by simpa only [haeq] using ha)
    hc rs (abs_le.mp hsc).1 rp rd hW (fun h => t ((hi _ _).mp h)))

/-- The auxiliary point follows by convex interpolation with the original
owned boundary point. -/
theorem point (Q A : OpenSquare) (ha : 1 < Q.side)
    (cap : Q.side ≤ 1001/1000)
    (p : Q.Inside (33/20) (33/20))
    (d : Q.Inside 2 (113/50))
    (w : Q.Inside 1 (87/50))
    (t : ¬ Q.Inside (33/20) (47/20))
    (e : ClosedInside A 2 (87/50))
    (m : ClosedInside A (113/50) 2)
    (apart : ∀ x y, ¬ (Q.Inside x y ∧ A.Inside x y)) :
    Q.Inside 1 (8/5) := by
  have low := point_low Q A ha cap p d w t e m apart
  exact ⟨by linarith only [low.1,w.1],by linarith only [low.2.1,w.2.1],
    by linarith only [low.2.2.1,w.2.2.1],
    by linarith only [low.2.2.2,w.2.2.2]⟩

#print axioms point_low
#print axioms point
end N12Compact.CentralWingReach
