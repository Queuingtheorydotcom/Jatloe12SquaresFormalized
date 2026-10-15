import Compact.Geometry.SouthwestNegativeCorner

/-! The positive-central sector when the left singleton misses its inner
corner is the transpose of the completed negative-central sector. The
reflection acts on actual complete squares and their owned points. -/
namespace N12Compact.SouthwestCornerTranspose

open S12 S12Pilot FourSquareAnchors C977CornerCubic

theorem point (O A L : OpenSquare) (normalA : Normal A.c A.s)
    (same : L.side=A.side) (side : 1<A.side) (box : InsideContainer L)
    (lM : L.Inside (457/500) 1) (lN : L.Inside 1 (28/25))
    (lF : L.Inside (19/25) (187/100))
    (missing : ¬L.Inside 1 1) (missingM : ¬L.Inside (457/500) 2)
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aE : A.Inside (87/50) 2) (aNew : A.Inside 2 (3/2))
    (oN : O.Inside (28/25) 1) (oW : O.Inside (87/50) 1)
    (la : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y))
    (ao : ∀ x y, ¬(A.Inside x y ∧ O.Inside x y)) : A.Inside 2 2 := by
  let r := turnFrame (turnFrame (turnFrame (pullSwap A)))
  have inside : ∀ x y, r.Inside x y ↔ A.Inside y x := by
    intro x y
    simp only [r,turnFrame_inside,inside_pullSwap]
  have normalR : Normal r.c A.s := by
    simpa only [r,turnFrame,pullSwap,neg_neg] using normalA
  have rs : r.s = -A.s := by simp only [r,turnFrame,pullSwap,neg_neg]
  have shape : r.side=A.side := rfl
  have lsame : (pullSwap L).side=r.side := same.trans shape.symm
  have reach := SouthwestNegativeCorner.point (pullSwap L) r (pullSwap O)
    A.s rs normalR lsame (by rw [shape]; exact side)
    (container_pullSwap _ box)
    ((inside_pullSwap _ _ _).mpr lM)
    ((inside_pullSwap _ _ _).mpr lN)
    ((inside_pullSwap _ _ _).mpr lF)
    (fun h => missing ((inside_pullSwap _ _ _).mp h))
    (fun h => missingM ((inside_pullSwap _ _ _).mp h))
    ((inside _ _).mpr aP) ((inside _ _).mpr aE)
    ((inside _ _).mpr aD) ((inside _ _).mpr aNew)
    ((inside_pullSwap _ _ _).mpr oN)
    ((inside_pullSwap _ _ _).mpr oW)
    (fun x y h => la y x ⟨(inside_pullSwap _ _ _).mp h.1,(inside x y).mp h.2⟩)
    (fun x y h => ao y x ⟨(inside x y).mp h.1,(inside_pullSwap _ _ _).mp h.2⟩)
  exact (inside 2 2).mp reach

end N12Compact.SouthwestCornerTranspose
