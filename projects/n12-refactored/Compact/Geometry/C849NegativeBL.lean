import Compact.Geometry.C849NegativePoints
import Compact.Geometry.ABTransverse

/-! The original negative-frame B triangle and actual L square leave only
two oriented separating faces. All discarded axes are eliminated by strict
points or the side greater than one; there is no angle discretization. -/
namespace N12Compact.C849NegativeBL
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse

theorem left_inward_of_lower_U (L : OpenSquare)
    (lc : 0 < L.c) (canonical : |L.s| ≤ L.c) (ha : 1 < L.side)
    (left : ClosedInside L (457/500) 2) (top : ClosedInside L 1 (12/5))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (below : L.c*(19/25)+L.s*(187/100) ≤ L.loU) :
    L.Inside (7/5) (13/5) := by
  have bounds := abs_le.mp canonical
  have lowerU : L.loU < L.c*(33/20)+L.s*(33/20) := by
    linarith only [left.1,bounds.2,lc]
  have upperU : L.c*(33/20)+L.s*(33/20) < L.loU+L.side := by
    have short := (short_projections L (89/100) (-(11/50)) (by norm_num)).2.1
    linarith only [below,short,ha]
  have upperV : -L.s*(33/20)+L.c*(33/20) < L.loV+L.side := by
    linarith only [top.2.2.2,bounds.1,lc]
  have belowV : -L.s*(33/20)+L.c*(33/20) ≤ L.loV :=
    le_of_not_gt (fun hp => missingRight ⟨lowerU,upperU,hp,upperV⟩)
  have shortU := (short_projections L (16/25) (73/100) (by norm_num)).2.1
  have shortV := (short_projections L (-(1/4)) (19/20) (by norm_num)).2.2.2
  exact ⟨by linarith only [top.1,bounds.1,lc],
    by linarith only [below,shortU,ha],
    by linarith only [left.2.2.1,bounds.2,lc],
    by linarith only [belowV,shortV,ha]⟩

theorem lower_V (L : OpenSquare)
    (lc : 0 < L.c) (canonical : |L.s| ≤ L.c) (ha : 1 < L.side)
    (left : ClosedInside L (457/500) 2) (top : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (missingInward : ¬ L.Inside (7/5) (13/5)) :
    -L.s*(19/25)+L.c*(187/100) ≤ L.loV := by
  have bounds := abs_le.mp canonical
  have upperU : L.c*(19/25)+L.s*(187/100) < L.loU+L.side := by
    linarith only [left.2.1,bounds.1,lc]
  have upperV : -L.s*(19/25)+L.c*(187/100) < L.loV+L.side := by
    linarith only [top.2.2.2,bounds.2,lc]
  have lowerU : L.loU < L.c*(19/25)+L.s*(187/100) := by
    apply lt_of_not_ge
    intro below
    exact missingInward (left_inward_of_lower_U L lc canonical ha left top missingRight below)
  exact le_of_not_gt (fun hp => missingLow ⟨lowerU,upperU,hp,upperV⟩)

/-- Both transverse faces of L contain B's fixed interior point. -/
theorem inward_V_band (L : OpenSquare)
    (lc : 0 < L.c) (canonical : |L.s| ≤ L.c) (ha : 1 < L.side)
    (left : ClosedInside L (457/500) 2)
    (below : -L.s*(19/25)+L.c*(187/100) ≤ L.loV) :
    L.loV < -L.s*(7/5)+L.c*(13/5) ∧
      -L.s*(7/5)+L.c*(13/5) < L.loV+L.side := by
  have bounds := abs_le.mp canonical
  have short := (short_projections L (16/25) (73/100) (by norm_num)).2.2.2
  exact ⟨by linarith only [left.2.2.1,bounds.2,lc],
    by linarith only [below,short,ha]⟩

/-- The genuine B/L disjointness reduces to two directed inequalities. -/
theorem alternatives (B L : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < B.side) (same : B.side=L.side)
    (bottom : B.Inside (33/20) (47/20)) (high : B.Inside 2 (1543/500))
    (missingA : ¬ B.Inside 2 (5/2))
    (left : ClosedInside L (457/500) 2) (top : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) :
    (-L.s*(19/25)+L.c*(187/100) ≤ L.loV) ∧
      (upper L (-B.s) B.c ≤ B.loV ∨
        L.loU+L.side ≤ lower B L.c L.s) := by
  have inward := C849NegativePoints.inward_point B bc bs bsc ha bottom high missingA
  have lha : 1 < L.side := by simpa only [same] using ha
  have low := lower_V L lc lsc lha left top missingLow missingRight
    (fun hp => apart _ _ ⟨inward,hp⟩)
  refine ⟨low,?_⟩
  have band := inward_V_band L lc lsc lha left low
  have cap := C849NegativePoints.upper_face B bc bs bsc bottom high missingA
  have bclosed : ClosedInside B (33/20) (47/20) :=
    ⟨bottom.1.le,bottom.2.1.le,bottom.2.2.1.le,bottom.2.2.2.le⟩
  have bounds := abs_le.mp lsc
  have axes := CongruentSAT.faceSeparation_of_disjoint B L same apart
  change pairRadius B L ≤ |B.c*(centerX L-centerX B)+B.s*(centerY L-centerY B)| ∨
    pairRadius B L ≤ |-B.s*(centerX L-centerX B)+B.c*(centerY L-centerY B)| ∨
    pairRadius L B ≤ |L.c*(centerX L-centerX B)+L.s*(centerY L-centerY B)| ∨
    pairRadius L B ≤ |-L.s*(centerX L-centerX B)+L.c*(centerY L-centerY B)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius B nx ny+supportRadius L nx ny=R)
      (sep : R ≤ |nx*(centerX L-centerX B)+ny*(centerY L-centerY B)|) :=
    separated B L nx ny (by rwa [identity])
  rcases axes with bu | bv | lu | lv
  · have sep := separateAxis B.c B.s _ (parallel_radius B L) bu
    have lp := closed_bounds L _ _ B.c B.s left
    have lq := closed_bounds L _ _ B.c B.s top
    have bp := strict_bounds B _ _ B.c B.s B.unit_normal bottom
    rcases sep with sep | sep
    · exfalso
      nlinarith only [sep,lp.1,bp.2,bc,bsc]
    · rw [(ownU B).1] at sep
      have one : B.c ≤ 1 := by nlinarith only [B.unit_normal,sq_nonneg B.s]
      exfalso
      nlinarith only [sep,lq.2,cap,ha,bs,one]
  · have sep := separateAxis (-B.s) B.c _ (transverse_radius B L) bv
    have lp := closed_bounds L _ _ (-B.s) B.c left
    have bp := strict_bounds B _ _ (-B.s) B.c
      (by nlinarith only [B.unit_normal]) bottom
    rcases sep with sep | sep
    · exfalso
      nlinarith only [sep,lp.1,bp.2,bc,bs]
    · left
      simpa only [(ownV B).1] using sep
  · have radius : supportRadius B L.c L.s+supportRadius L L.c L.s=pairRadius L B := by
      rw [add_comm]; exact parallel_radius L B
    have sep := separateAxis L.c L.s _ radius lu
    have lp := closed_bounds L _ _ L.c L.s top
    have bp := strict_bounds B _ _ L.c L.s L.unit_normal bottom
    rcases sep with sep | sep
    · exfalso
      nlinarith only [sep,lp.1,bp.2,lc,bounds.2]
    · right
      simpa only [(ownU L).2] using sep
  · have radius : supportRadius B (-L.s) L.c+supportRadius L (-L.s) L.c=pairRadius L B := by
      rw [add_comm]; exact transverse_radius L B
    have sep := separateAxis (-L.s) L.c _ radius lv
    have bp := strict_bounds B _ _ (-L.s) L.c
      (by nlinarith only [L.unit_normal]) inward
    rw [(ownV L).1,(ownV L).2] at sep
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bp.1,bp.2,band.1,band.2]

#print axioms alternatives
end N12Compact.C849NegativeBL
