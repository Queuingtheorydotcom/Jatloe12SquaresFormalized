import Compact.Geometry.MergedLeftEscape
import S12.ShortCluster

/-! The original lower-left corner points remove the steep escape of a
merged left central square. These are genuine foreign auxiliary points,
not an assumed auxiliary count or an assumed neighboring support line.
The remaining shallow sector still needs the actual wall interaction. -/
namespace N12Compact.MergedLeftCornerSector
open S12 S12Pilot
set_option Elab.async false

/-- The upper-V alternative at (1,1.74) would put the original corner's
point (1.6,1) strictly inside the merged central square. -/
theorem corner_point (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (cap : A.loU+A.side ≤ 2*(A.c+A.s))
    (upper : A.loV+A.side ≤ (87/50)*A.c-A.s) :
    A.Inside (8/5) 1 := by
  have sum : A.c+A.s ≤ 10/7 := by
    nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s),hc,hs]
  have along : (2/5)*A.c+A.s ≤ 1 := by
    linarith only [sum,order]
  have across := (short_projections A (37/50) (3/5) (by norm_num)).2.1
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,along]
  · linarith only [bottom.2.1,hc,hs]
  · linarith only [upper,side,across]
  · linarith only [top.2.2.2,hc,order]

/-- Both missing points belong to original lower corner owners. Their
exclusion therefore selects A's lower-U face without a wall-angle split. -/
theorem lower_u (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (center : ¬ A.Inside 2 2)
    (left : ¬ A.Inside 1 (87/50))
    (corner : ¬ A.Inside (8/5) 1) :
    A.c+(87/50)*A.s ≤ A.loU := by
  have cap := MergedLeftEscape.center_cap A hc hs order bottom top center
  exact (MergedLeftEscape.left_aux_faces A hc hs bottom top left).resolve_right
    (fun upper => corner (corner_point A side hc hs order bottom top cap upper))

/-- The surviving escape angle is strictly between zero and the rational
slope 1300/2331. The bound follows from the exact side inequality
`1 < side ≤ c + (13/50)s` and the unit-normal identity. -/
theorem sector (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (center : ¬ A.Inside 2 2)
    (left : ¬ A.Inside 1 (87/50))
    (corner : ¬ A.Inside (8/5) 1) :
    A.side ≤ A.c+(13/50)*A.s ∧ 0 < A.s ∧ 2331*A.s < 1300*A.c := by
  have cap := MergedLeftEscape.center_cap A hc hs order bottom top center
  have low := lower_u A side hc hs order bottom top center left corner
  have width : A.side ≤ A.c+(13/50)*A.s := by linarith only [cap,low]
  have cu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  have positive : 0 < A.s := by linarith only [width,side,cu]
  have strict : 1 < A.c+(13/50)*A.s := lt_of_lt_of_le side width
  have square := mul_pos (sub_pos.mpr strict)
    (show 0 < A.c+(13/50)*A.s+1 by linarith only [hc,hs])
  have slope : 2331*A.s < 1300*A.c := by
    by_contra no
    have product := mul_nonneg hs (sub_nonneg.mpr (le_of_not_gt no))
    nlinarith only [square,product,A.unit_normal]
  exact ⟨width,positive,slope⟩

#print axioms sector
end N12Compact.MergedLeftCornerSector
