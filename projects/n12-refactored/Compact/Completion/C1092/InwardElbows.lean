import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The all-orientation inward-elbow entrance from retained/walls/02.
Only the strict original central marker, six genuine exclusions and side > 1
are premises. No angle, center, auxiliary assignment or containment premise
is added. The final adapters retain the physical owners separately. -/
namespace N12Compact.C1092InwardElbows
open S12 S12Pilot
set_option Elab.async false

private theorem positive_pair (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (33/20) (33/20))
    (east : ¬ q.Inside (47/20) (33/20))
    (north : ¬ q.Inside (33/20) (47/20))
    (leftLow : ¬ q.Inside 1 (803/500))
    (leftAux : ¬ q.Inside 1 (87/50))
    (bottomLow : ¬ q.Inside (803/500) 1) :
    q.Inside 2 (87/50) ∧ q.Inside (87/50) 2 := by
  classical
  obtain ⟨m0,m1,m2,m3⟩ := marker
  have hc1 : q.c ≤ 1 := by nlinarith [q.unit_normal,sq_nonneg q.s]
  have hs1 : q.s ≤ 1 := order.trans hc1
  have dNP := short_projections q (33/20-1) (47/20-803/500) (by norm_num)
  have dND := short_projections q (33/20-2) (47/20-87/50) (by norm_num)
  have dDB := short_projections q (2-803/500) (87/50-1) (by norm_num)
  have dLB := short_projections q (1-803/500) (87/50-1) (by norm_num)
  have dEB := short_projections q (47/20-803/500) (33/20-1) (by norm_num)
  have dDE := short_projections q (2-47/20) (87/50-33/20) (by norm_num)
  have dFE := short_projections q (87/50-47/20) (2-33/20) (by norm_num)
  have d0 : q.loU < q.c*2+q.s*(87/50) := by
    linarith only [m0,hc,hs]
  have d2 : q.loV < -q.s*2+q.c*(87/50) := by
    by_contra absent
    have low : -q.s*2+q.c*(87/50) ≤ q.loV := le_of_not_gt absent
    have nu0 : q.loU < q.c*(33/20)+q.s*(47/20) := by
      linarith only [m0,hs]
    have nv0 : q.loV < -q.s*(33/20)+q.c*(47/20) := by
      linarith only [m2,hc]
    have nv1 : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
      linarith only [low,ha,dND.2.2.2]
    have nu1 : q.loU+q.side ≤ q.c*(33/20)+q.s*(47/20) := by
      exact le_of_not_gt (fun h => north ⟨nu0,h,nv0,nv1⟩)
    apply leftLow
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [nu1,ha,dNP.2.1]
    · linarith only [m1,hc,hs]
    · linarith only [m2,low,hc]
    · linarith only [low,ha,hs1,hc]
  have d1 : q.c*2+q.s*(87/50) < q.loU+q.side := by
    by_contra absent
    have high : q.loU+q.side ≤ q.c*2+q.s*(87/50) := le_of_not_gt absent
    have bu0 : q.loU < q.c*(803/500)+q.s := by
      linarith only [high,ha,dDB.2.1]
    have bu1 : q.c*(803/500)+q.s < q.loU+q.side := by
      linarith only [m1,hc,hs]
    have bv1 : -q.s*(803/500)+q.c < q.loV+q.side := by
      linarith only [m3,hc,order]
    have bv0 : -q.s*(803/500)+q.c ≤ q.loV := by
      apply le_of_not_gt
      intro h
      apply bottomLow
      simpa only [OpenSquare.Inside,InBands,mul_one] using And.intro bu0
        (And.intro bu1 (And.intro h bv1))
    apply leftAux
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [high,ha,hc1]
    · linarith only [m1,hc,order]
    · linarith only [m2,hc,hs]
    · linarith only [bv0,ha,dLB.2.2.2]
  have upperV (x y : ℝ)
      (re : -q.s*(x-47/20)+q.c*(y-33/20) ≤ 1)
      (rb : -q.s*(x-803/500)+q.c*(y-1) ≤ 1) :
      -q.s*x+q.c*y < q.loV+q.side := by
    by_contra absent
    have high : q.loV+q.side ≤ -q.s*x+q.c*y := le_of_not_gt absent
    have eu0 : q.loU < q.c*(47/20)+q.s*(33/20) := by
      linarith only [m0,hc]
    have ev0 : q.loV < -q.s*(47/20)+q.c*(33/20) := by
      linarith only [high,ha,re]
    have ev1 : -q.s*(47/20)+q.c*(33/20) < q.loV+q.side := by
      linarith only [m3,hs]
    have eu1 : q.loU+q.side ≤ q.c*(47/20)+q.s*(33/20) :=
      le_of_not_gt (fun h => east ⟨eu0,h,ev0,ev1⟩)
    apply bottomLow
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [eu1,ha,dEB.2.1]
    · linarith only [m1,hc,hs]
    · linarith only [high,ha,rb]
    · linarith only [m3,hc,order]
  have d3 : -q.s*2+q.c*(87/50) < q.loV+q.side :=
    upperV 2 (87/50) dDE.2.2.2 dDB.2.2.2
  have f3 : -q.s*(87/50)+q.c*2 < q.loV+q.side :=
    upperV (87/50) 2 dFE.2.2.2 (by linarith only [hc1,hs])
  exact ⟨⟨d0,d1,d2,d3⟩,
    ⟨by linarith only [m0,hc,hs],by linarith only [d1,order],
      by linarith only [m2,hc,order],f3⟩⟩

/-- A signed canonical frame can be transposed without changing any
strict or weak band. This swaps the two target elbows simultaneously. -/
private noncomputable def swapFrame (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith [q.unit_normal]
  side_pos := q.side_pos

private theorem swapFrame_inside (q : OpenSquare) (x y : ℝ) :
    (swapFrame q).Inside x y ↔ q.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Whole physical-square entrance. Face exits are weak; conclusions are
strict even on the axial and diagonal orientation endpoints. -/
theorem pair (q : OpenSquare) (ha : 1 < q.side)
    (marker : q.Inside (33/20) (33/20))
    (east : ¬ q.Inside (47/20) (33/20))
    (north : ¬ q.Inside (33/20) (47/20))
    (leftLow : ¬ q.Inside 1 (803/500))
    (leftAux : ¬ q.Inside 1 (87/50))
    (bottomLow : ¬ q.Inside (803/500) 1)
    (bottomAux : ¬ q.Inside (87/50) 1) :
    q.Inside 2 (87/50) ∧ q.Inside (87/50) 2 := by
  obtain ⟨r,hc,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have hr : 1 < r.side := by simpa only [side] using ha
  have m := (inside _ _).mpr marker
  have e : ¬ r.Inside (47/20) (33/20) := fun h => east ((inside _ _).mp h)
  have n : ¬ r.Inside (33/20) (47/20) := fun h => north ((inside _ _).mp h)
  have l : ¬ r.Inside 1 (803/500) := fun h => leftLow ((inside _ _).mp h)
  have f : ¬ r.Inside 1 (87/50) := fun h => leftAux ((inside _ _).mp h)
  have b : ¬ r.Inside (803/500) 1 := fun h => bottomLow ((inside _ _).mp h)
  have j : ¬ r.Inside (87/50) 1 := fun h => bottomAux ((inside _ _).mp h)
  by_cases hs : 0 ≤ r.s
  · have result := positive_pair r hr hc hs
      (by simpa only [abs_of_nonneg hs] using range) m e n l f b
    exact ⟨(inside _ _).mp result.1,(inside _ _).mp result.2⟩
  · have result := positive_pair (swapFrame r) hr hc
      (by dsimp [swapFrame]; linarith only [hs])
      (by simpa only [swapFrame,abs_of_neg (lt_of_not_ge hs)] using range)
      ((swapFrame_inside _ _ _).mpr m)
      (fun h => n ((swapFrame_inside _ _ _).mp h))
      (fun h => e ((swapFrame_inside _ _ _).mp h))
      (fun h => b ((swapFrame_inside _ _ _).mp h))
      (fun h => j ((swapFrame_inside _ _ _).mp h))
      (fun h => l ((swapFrame_inside _ _ _).mp h))
    exact ⟨(inside _ _).mp ((swapFrame_inside _ _ _).mp result.2),
      (inside _ _).mp ((swapFrame_inside _ _ _).mp result.1)⟩

#print axioms pair
end N12Compact.C1092InwardElbows
