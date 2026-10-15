import S12.WallGeometry
import S12.Symmetry

/-!
A complete symbolic replacement for C981 InitialV116's 32 angle roots.
No angle discretization, side upper bound, container condition, or numerical
certificate is used. The strict interior / non-strict exterior boundary
conventions are unchanged.
-/

namespace N12Compact.C981Midpoint

open S12 S12Pilot

/-- In the shallow positive frame, the omitted lower point must fail the
lower first-coordinate face. Its distance to the forced midpoint is < 1. -/
theorem shallow (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s) (hsc : q.s ≤ q.c)
    (hA : q.Inside (113 / 50) 3) (hC : q.Inside 3 (113 / 50))
    (hD : ¬ q.Inside 2 (113 / 50)) : q.Inside (27 / 10) (27 / 10) := by
  obtain ⟨a0, a1, a2, a3⟩ := hA
  obtain ⟨c0, c1, c2, c3⟩ := hC
  have hDU : q.c * 2 + q.s * (113 / 50) ≤ q.loU := by
    by_contra hn
    apply hD
    dsimp [OpenSquare.Inside, InBands]
    exact ⟨by linarith only [hn], by linarith only [a1, hc, hs],
      by linarith only [c2, hs], by linarith only [a3, hc, hs, hsc]⟩
  have hlength := (short_projections q (7 / 10) (11 / 25) (by norm_num)).2.1
  dsimp [OpenSquare.Inside, InBands]
  exact ⟨by linarith only [a0, hc, hs, hsc],
    by linarith only [hDU, hlength, ha],
    by linarith only [c2, hc, hs], by linarith only [a3, hc, hs]⟩

/-- Four point conditions force one exact midpoint for every orientation,
including axis-aligned squares and equality at the diagonal frame split. -/
theorem forced_midpoint (q : OpenSquare) (ha : 1 < q.side)
    (hA : q.Inside (113 / 50) 3) (hC : q.Inside 3 (113 / 50))
    (hD : ¬ q.Inside 2 (113 / 50)) (hE : ¬ q.Inside (113 / 50) 2) :
    q.Inside (27 / 10) (27 / 10) := by
  obtain ⟨r, hc, hs, hside, _, _, hin⟩ := exists_positive_frame q
  have hrA := (hin (113 / 50) 3).mpr hA
  have hrC := (hin 3 (113 / 50)).mpr hC
  have hrD : ¬ r.Inside 2 (113 / 50) := fun h => hD ((hin _ _).mp h)
  have hrE : ¬ r.Inside (113 / 50) 2 := fun h => hE ((hin _ _).mp h)
  apply (hin _ _).mp
  by_cases hsc : r.s ≤ r.c
  · exact shallow r (by rw [hside]; exact ha) hc hs hsc hrA hrC hrD
  · have hswap := shallow (pullSwap r) (by simpa [pullSwap, hside] using ha)
      (by simpa [pullSwap] using hs) (by simpa [pullSwap] using hc)
      (by dsimp [pullSwap]; linarith only [hsc])
      ((inside_pullSwap r _ _).mpr hrC) ((inside_pullSwap r _ _).mpr hrA)
      (fun h => hrE ((inside_pullSwap r _ _).mp h))
    exact (inside_pullSwap r _ _).mp hswap

/-- The second owner contains the midpoint of its two strict owned points. -/
theorem foreign_midpoint (r : OpenSquare)
    (hF : r.Inside (12 / 5) 3) (hG : r.Inside 3 (12 / 5)) :
    r.Inside (27 / 10) (27 / 10) := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  obtain ⟨g0, g1, g2, g3⟩ := hG
  dsimp [OpenSquare.Inside, InBands]
  exact ⟨by linarith only [f0, g0], by linarith only [f1, g1],
    by linarith only [f2, g2], by linarith only [f3, g3]⟩

/-- Complete two-owner geometric contradiction used by representative 116. -/
theorem excludes (q r : OpenSquare) (ha : 1 < q.side)
    (hA : q.Inside (113 / 50) 3) (hC : q.Inside 3 (113 / 50))
    (hD : ¬ q.Inside 2 (113 / 50)) (hE : ¬ q.Inside (113 / 50) 2)
    (hF : r.Inside (12 / 5) 3) (hG : r.Inside 3 (12 / 5))
    (hd : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y)) : False :=
  hd (27 / 10) (27 / 10)
    ⟨forced_midpoint q ha hA hC hD hE, foreign_midpoint r hF hG⟩

end N12Compact.C981Midpoint
