import Compact.Geometry.WallLowerReach
import Compact.Completion.CommonCases.OriginalOwners
import S12.WallBridge

/-! The retained all-angle wall-reach argument at the exact parameters
w=8/5, d=87/50, z=206/85. This produces the inward chapters' shorter
right bar from the two genuine points of the opposite inward owner.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive_reach (q : OpenSquare) (side : 1<q.side)
    (cn : 0≤q.c) (sn : 0≤q.s)
    (wall : 0≤q.c*q.loU-q.s*(q.loV+q.side))
    (marker : q.Inside (457/500) 2) (anchor : q.Inside 1 (12/5))
    (low : ¬q.Inside 1 (8/5)) (diagonal : ¬q.Inside (87/50) 2) :
    q.Inside 1 (206/85) := by
  have product : 0≤q.c*q.s := mul_nonneg cn sn
  have sumLow : 1≤q.c+q.s := by nlinarith only [q.unit_normal,product,cn,sn]
  have sumHigh : q.c+q.s≤10/7 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),cn,sn]
  have chord := mul_nonneg (sub_nonneg.mpr sumHigh) (sub_nonneg.mpr sumLow)
  have arc : 1+(14/17)*q.c*q.s≤q.c+q.s := by nlinarith only [chord,q.unit_normal]
  have targetU : q.loU<q.c+(206/85)*q.s := by linarith only [marker.1,cn,sn]
  have targetV : q.loV< -q.s+(206/85)*q.c := by linarith only [anchor.2.2.1,cn]
  have diagonalU : q.loU<(87/50)*q.c+2*q.s := by linarith only [marker.1,cn]
  have diagonalV : -(87/50)*q.s+2*q.c<q.loV+q.side := by
    linarith only [anchor.2.2.2,cn,sn]
  have diagonalExit : q.loU+q.side≤(87/50)*q.c+2*q.s ∨
      -(87/50)*q.s+2*q.c≤q.loV := by
    by_cases exit : q.loU+q.side≤(87/50)*q.c+2*q.s
    · exact Or.inl exit
    · exact Or.inr (le_of_not_gt (fun below =>
        diagonal ⟨diagonalU,lt_of_not_ge exit,below,diagonalV⟩))
  have lowU : q.c+(8/5)*q.s<q.loU+q.side := by linarith only [anchor.2.1,sn]
  have lowV : -q.s+(8/5)*q.c<q.loV+q.side := by linarith only [marker.2.2.2,cn,sn]
  have lowExit : q.c+(8/5)*q.s≤q.loU ∨ -q.s+(8/5)*q.c≤q.loV := by
    by_cases exit : q.c+(8/5)*q.s≤q.loU
    · exact Or.inl exit
    · right
      apply le_of_not_gt
      intro below
      apply low
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [exit,lowU,lowV,below]
  have targetGap := short_projections q 0 (14/17) (by norm_num)
  rcases lowExit with u|v
  · have gap := (short_projections q (37/50) (2/5) (by norm_num)).2.1
    have lowerV : -(87/50)*q.s+2*q.c≤q.loV := by
      rcases diagonalExit with upperU|lowerV
      · exact False.elim (by linarith only [u,upperU,gap,side])
      · exact lowerV
    have finalGap := (short_projections q (-37/50) (36/85) (by norm_num)).2.2.2
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [targetU,targetV,u,lowerV,targetGap.2.1,finalGap,side]
  · have wallTerm := mul_nonneg sn (sub_nonneg.mpr v)
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<q.c+q.s by linarith only [sumLow])
    have upperU : q.c+(206/85)*q.s<q.loU+q.side := by
      apply lt_of_not_ge
      intro no
      have upperTerm := mul_nonneg cn (sub_nonneg.mpr no)
      nlinarith only [wall,wallTerm,strict,upperTerm,arc,q.unit_normal]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [targetU,targetV,upperU,v,targetGap.2.2.2,side]

theorem left_reach (q : OpenSquare) (side : 1<q.side)
    (wall : ∀ x y,q.Inside x y → 0≤x)
    (marker : q.Inside (457/500) 2) (anchor : q.Inside 1 (12/5))
    (low : ¬q.Inside 1 (8/5)) (diagonal : ¬q.Inside (87/50) 2) :
    q.Inside 1 (206/85) := by
  obtain ⟨r,cn,sn,same,_,_,inside⟩ := exists_positive_frame q
  have actualWall : ∀ x y,r.Inside x y → 0≤x :=
    fun x y own => wall x y ((inside x y).mp own)
  exact (inside _ _).mp (positive_reach r (by simpa only [same] using side)
    cn sn (left_wall_vertex r actualWall) ((inside _ _).mpr marker)
    ((inside _ _).mpr anchor) (fun own => low ((inside _ _).mp own))
    (fun own => diagonal ((inside _ _).mp own)))

/-- Original coordinates: only actual N's G9/G6 are used. F9 and an
ordinary opposite are not premises. R remains the same actual square
throughout the half-turn and the final entire segment. -/
theorem right_bar (R N : OpenSquare) (side : 1<R.side)
    (wall : ∀ x y,R.Inside x y → x≤4)
    (marker : R.Inside (1543/500) 2) (anchor : R.Inside 3 (8/5))
    (origin : R.Inside 3 2) (outer : N.Inside 3 (12/5))
    (inner : N.Inside (113/50) 2)
    (apart : ∀ x y,¬(R.Inside x y ∧ N.Inside x y)) :
    ∀ y : ℝ,-36/85≤y → y≤0 → (R.translated 2 2).Inside 1 y := by
  let T := pullX (pullY R)
  have ti (x y : ℝ) : T.Inside x y ↔ R.Inside (4-x) (4-y) := by
    simp only [T,inside_pullX,inside_pullY]
  have high := left_reach T side
    (fun x y own => by have actual := wall _ _ ((ti x y).mp own); linarith only [actual])
    (by rw [ti]; norm_num; exact marker)
    (by rw [ti]; norm_num; exact anchor)
    (fun own => apart _ _ ⟨by have actual := (ti 1 (8/5)).mp own; norm_num at actual; exact actual,outer⟩)
    (fun own => apart _ _ ⟨by have actual := (ti (87/50) 2).mp own; norm_num at actual; exact actual,inner⟩)
  have far : R.Inside 3 (134/85) := by
    have actual := (ti 1 (206/85)).mp high
    norm_num at actual
    exact actual
  intro y low high
  rw [inside_translated_iff]
  norm_num
  exact CommonCases.OriginalOwners.vertical_segment R 3 (134/85) 2 (2+y)
    far origin (by norm_num) (by linarith only [low]) (by linarith only [high])

#print axioms left_reach
#print axioms right_bar
end N12Compact.C1092MPPMInwardFinal
