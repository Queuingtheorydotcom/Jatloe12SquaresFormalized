import Compact.Geometry.MergedLeftCornerSector
import Compact.Geometry.MergedRightWallSector
import S12.TransformFacts

/-! The whole nonpositive canonical-angle sector of the original merged
left central owner. The only foreign auxiliary points are genuinely
owned by the lower corner, left wall, and top wall in the intended
families. The left wall keeps its full container and disjointness. -/
namespace N12Compact.MergedLeftNegative
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem point (A L : OpenSquare) (side : 1 < A.side)
    (same : A.side=L.side) (box : InsideContainer L)
    (hc : 0 < A.c) (negative : A.s ≤ 0) (canonical : -A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20)) (top : A.Inside (33/20) (47/20))
    (low : ¬ A.Inside 1 (87/50)) (high : ¬ A.Inside 1 (113/50))
    (topCorner : ¬ A.Inside (8/5) 3)
    (marker : L.Inside (457/500) 2) (wallHigh : L.Inside 1 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ L.Inside x y)) : A.Inside 2 2 := by
  by_contra center
  have sector := MergedLeftCornerSector.sector (pullY A) side hc
    (by dsimp [pullY]; linarith only [negative]) canonical
    ((inside_pullY A _ _).mpr (by convert top using 1 <;> norm_num))
    ((inside_pullY A _ _).mpr (by convert bottom using 1 <;> norm_num))
    (fun h => center (by convert (inside_pullY A _ _).mp h using 1 <;> norm_num))
    (fun h => high (by convert (inside_pullY A _ _).mp h using 1 <;> norm_num))
    (fun h => topCorner (by convert (inside_pullY A _ _).mp h using 1 <;> norm_num))
  have shallow : -A.s ≤ (16/25)*A.c := by
    have bound := sector.2.2
    dsimp [pullY] at bound
    linarith only [bound,hc]
  let B := turnFrame (turnFrame (pullX A))
  have inside (x y : ℝ) : B.Inside x y ↔ A.Inside (4-x) y := by
    dsimp [B]
    simp only [turnFrame_inside,inside_pullX]
  have bc : B.c=A.c := by dsimp [B,turnFrame,pullX]; ring
  have bs : B.s=-A.s := by dsimp [B,turnFrame,pullX]
  have result := MergedRightWallSector.point B (pullX L) side same
    (container_pullX L box)
    (by simpa only [bc] using hc)
    (by rw [bs]; linarith only [negative])
    (by simpa only [bc,bs] using shallow)
    ((inside _ _).mpr (by convert bottom using 1 <;> norm_num))
    ((inside _ _).mpr (by convert top using 1 <;> norm_num))
    (fun h => low (by convert (inside _ _).mp h using 1 <;> norm_num))
    ((inside_pullX L _ _).mpr (by convert marker using 1 <;> norm_num))
    ((inside_pullX L _ _).mpr (by convert wallHigh using 1 <;> norm_num))
    (fun x y h => apart (4-x) y
      ⟨(inside x y).mp h.1,(inside_pullX L x y).mp h.2⟩)
  apply center
  convert (inside 2 2).mp result using 1 <;> norm_num

#print axioms point
end N12Compact.MergedLeftNegative
