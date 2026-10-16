import Compact.Geometry.FourSquareANarrow
import Compact.Geometry.ClosedFrames
import S12.Convex

/-! Strict central crosspoints from three owned points, the other three
missing central markers, and an actual foreign singleton segment. Every
orientation is covered by face reindexing; no pose enclosure is assumed. -/
namespace N12Compact.SouthwestCentralReach

open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

/-- The narrow central-square implication, with its orientation normalization
performed internally and all excluded points retained as original premises. -/
theorem northeast (A : OpenSquare) (ha : 1 < A.side)
    (hP : A.Inside 2 (113/50)) (hQ : A.Inside (113/50) 2)
    (hT : A.Inside (47/20) (47/20))
    (hF : ¬ A.Inside (33/20) (33/20))
    (hG : ¬ A.Inside (47/20) (33/20))
    (hB : ¬ A.Inside (33/20) (47/20))
    (hR : ¬ A.Inside 3 (12/5)) (hH : ¬ A.Inside 3 (5/2)) :
    A.Inside 2 (5/2) := by
  obtain ⟨q,hc,hs,side,inside,closed⟩ := ClosedFrames.positive_frame A
  apply (inside _ _).mp
  exact FourSquareANarrow.point_of_higher_R q (by rw [side]; exact ha) hc hs
    ((closed _ _).mpr (close hP)) ((closed _ _).mpr (close hQ))
    ((closed _ _).mpr (close hT))
    (fun h => hF ((inside _ _).mp h))
    (fun h => hG ((inside _ _).mp h))
    (fun h => hB ((inside _ _).mp h))
    (fun h => hR ((inside _ _).mp h))
    (fun h => hH ((inside _ _).mp h))

/-- A left singleton seed segment forces the lower strict central crosspoint.
The foreign square is used through actual interior disjointness. -/
theorem below (A L : OpenSquare) (ha : 1 < A.side)
    (hP : A.Inside (33/20) (33/20))
    (hD : A.Inside 2 (87/50)) (hE : A.Inside (87/50) 2)
    (hNE : ¬ A.Inside (47/20) (47/20))
    (hNW : ¬ A.Inside (33/20) (47/20))
    (hSE : ¬ A.Inside (47/20) (33/20))
    (hN : L.Inside 1 (28/25)) (hW : L.Inside 1 (87/50))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ L.Inside x y)) :
    A.Inside 2 (3/2) := by
  have lLow : L.Inside 1 (3/2) := by
    have point := inside_segment L 1 (28/25) 1 (87/50) (19/31)
      hN hW (by norm_num) (by norm_num)
    convert point using 1 <;> norm_num
  have lHigh : L.Inside 1 (8/5) := by
    have point := inside_segment L 1 (28/25) 1 (87/50) (24/31)
      hN hW (by norm_num) (by norm_num)
    convert point using 1 <;> norm_num
  have missingLow : ¬ A.Inside 1 (3/2) := fun h => apart _ _ ⟨h,lLow⟩
  have missingHigh : ¬ A.Inside 1 (8/5) := fun h => apart _ _ ⟨h,lHigh⟩
  have reach := northeast (pullX (pullY A))
    (by change 1 < A.side; exact ha)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hD)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hE)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hP)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hNE)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hNW)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact hSE)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact missingHigh)
    (by rw [inside_pullX,inside_pullY]; norm_num only; exact missingLow)
  rw [inside_pullX,inside_pullY] at reach
  norm_num only at reach
  exact reach

/-- Coordinate transposition gives the left strict crosspoint from the
bottom singleton's original horizontal seed segment. -/
theorem left (A O : OpenSquare) (ha : 1 < A.side)
    (hP : A.Inside (33/20) (33/20))
    (hD : A.Inside 2 (87/50)) (hE : A.Inside (87/50) 2)
    (hNE : ¬ A.Inside (47/20) (47/20))
    (hNW : ¬ A.Inside (33/20) (47/20))
    (hSE : ¬ A.Inside (47/20) (33/20))
    (hN : O.Inside (28/25) 1) (hW : O.Inside (87/50) 1)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ O.Inside x y)) :
    A.Inside (3/2) 2 := by
  have reach := below (pullSwap A) (pullSwap O) ha
    ((inside_pullSwap _ _ _).mpr hP)
    ((inside_pullSwap _ _ _).mpr hE)
    ((inside_pullSwap _ _ _).mpr hD)
    (by simpa only [inside_pullSwap] using hNE)
    (by simpa only [inside_pullSwap] using hSE)
    (by simpa only [inside_pullSwap] using hNW)
    ((inside_pullSwap _ _ _).mpr hN)
    ((inside_pullSwap _ _ _).mpr hW)
    (fun x y h => apart y x
      ⟨(inside_pullSwap _ _ _).mp h.1,(inside_pullSwap _ _ _).mp h.2⟩)
  exact (inside_pullSwap _ _ _).mp reach

end N12Compact.SouthwestCentralReach
