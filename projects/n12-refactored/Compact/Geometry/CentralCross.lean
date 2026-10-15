import Compact.Geometry.FourSquareAForced
import Compact.Geometry.ClosedFrames

/-! A local central owner must reach one of two perpendicular cuts.
The hypotheses are symmetric under swapping coordinates, so one shallow
frame argument covers every orientation. No wall or pose cover is assumed.
This is a propagation lemma, not a whole-case exclusion. -/

namespace N12Compact.CentralCross

open S12 S12Pilot FourSquareAnchors

private theorem closed_swap (q : OpenSquare) (x y : ℝ) :
    ClosedInside (pullSwap q) x y ↔ ClosedInside q y x := by
  dsimp [ClosedInside, pullSwap]
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem point (q : OpenSquare) (ha : 1 < q.side)
    (hP : ClosedInside q 2 (113/50))
    (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hF : ¬ q.Inside (33/20) (33/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20))
    (hR : ¬ q.Inside 3 (12/5))
    (hTop : ¬ q.Inside (12/5) 3) :
    q.Inside 2 (5/2) ∨ q.Inside (5/2) 2 := by
  obtain ⟨r,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame q
  have hra : 1 < r.side := by simpa only [hside] using ha
  have hp := (hcl _ _).mpr hP
  have hq := (hcl _ _).mpr hQ
  have ht := (hcl _ _).mpr hT
  have hf : ¬ r.Inside (33/20) (33/20) := fun h => hF ((hi _ _).mp h)
  have hg : ¬ r.Inside (47/20) (33/20) := fun h => hG ((hi _ _).mp h)
  have hb : ¬ r.Inside (33/20) (47/20) := fun h => hB ((hi _ _).mp h)
  have hr : ¬ r.Inside 3 (12/5) := fun h => hR ((hi _ _).mp h)
  have htop : ¬ r.Inside (12/5) 3 := fun h => hTop ((hi _ _).mp h)
  by_cases hzero : r.s = 0
  · have hone : r.c = 1 := by nlinarith [r.unit_normal]
    exact Or.inl ((hi _ _).mp
      (FourSquareAForced.axis_point r hra hone hzero hp hq ht hf hg hr))
  have hsp : 0 < r.s := lt_of_le_of_ne hs (Ne.symm hzero)
  by_cases hshallow : r.s ≤ r.c
  · exact Or.inl ((hi _ _).mp
      (FourSquareAForced.positive_shallow_point r hra hc.le hsp hshallow
        hp hq ht hg hb hr))
  · have target : (pullSwap r).Inside 2 (5/2) :=
      FourSquareAForced.positive_shallow_point (pullSwap r) hra hs hc
        (by dsimp [pullSwap]; exact (lt_of_not_ge hshallow).le)
        ((closed_swap r _ _).mpr hq) ((closed_swap r _ _).mpr hp)
        ((closed_swap r _ _).mpr ht)
        (fun h => hb ((inside_pullSwap r _ _).mp h))
        (fun h => hg ((inside_pullSwap r _ _).mp h))
        (fun h => htop ((inside_pullSwap r _ _).mp h))
    exact Or.inr ((hi _ _).mp ((inside_pullSwap r _ _).mp target))

theorem cut_point (q : OpenSquare) (ha : 1 < q.side)
    (hP : ClosedInside q 2 (113/50))
    (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hF : ¬ q.Inside (33/20) (33/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20))
    (hR : ¬ q.Inside 3 (12/5))
    (hTop : ¬ q.Inside (12/5) 3) :
    q.Inside 2 (12/5) ∨ q.Inside (12/5) 2 := by
  rcases point q ha hP hQ hT hF hG hB hR hTop with vertical | horizontal
  · exact Or.inl (FourSquareAForced.row_point q hP vertical)
  · have h := FourSquareAForced.row_point (pullSwap q)
      ((closed_swap q _ _).mpr hQ) ((inside_pullSwap q _ _).mpr horizontal)
    exact Or.inr ((inside_pullSwap q _ _).mp h)

#print axioms point
#print axioms cut_point
end N12Compact.CentralCross
