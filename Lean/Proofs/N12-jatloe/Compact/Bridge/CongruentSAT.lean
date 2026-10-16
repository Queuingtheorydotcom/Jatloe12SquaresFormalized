import Compact.Geometry.ScalarSATSigned
import Compact.Geometry.C977ChainBridge
import Mathlib.Tactic.FieldSimp

/-!
Separating axes for the original OpenSquare model with equal side lengths.
The scalar overlap theorem is transported by the first square's orthonormal
frame and its positive half-side. Thus all orientations, zero components,
and legal boundary contact are included. No overlap or SAT premise is added.
The equal-side hypothesis is exactly available in NormalizedPacking.
-/

namespace N12Compact.CongruentSAT

open S12 S12Pilot S12Completion.C977 C977ChainBridge

/-- Disjoint congruent original squares have a weak separating face axis. -/
theorem faceSeparation_of_disjoint (q r : OpenSquare)
    (hside : q.side = r.side)
    (hd : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y)) :
    FaceSeparation q r := by
  let f := q.side / 2
  let c := normalDot q r
  let s := normalCross q r
  let dx := centerX r - centerX q
  let dy := centerY r - centerY q
  let X := (q.c * dx + q.s * dy) / f
  let Y := (-q.s * dx + q.c * dy) / f
  let U := (r.c * dx + r.s * dy) / f
  let V := (-r.s * dx + r.c * dy) / f
  have hf : 0 < f := div_pos q.side_pos (by norm_num)
  have hunit : c ^ 2 + s ^ 2 = 1 := by
    calc
      _ = (q.c ^ 2 + q.s ^ 2) * (r.c ^ 2 + r.s ^ 2) := by
        dsimp [c, s, normalDot, normalCross]; ring
      _ = 1 := by rw [q.unit_normal, r.unit_normal]; ring
  have hU : U = c * X + s * Y := by
    have he : c * (q.c * dx + q.s * dy) + s * (-q.s * dx + q.c * dy) =
        r.c * dx + r.s * dy := by
      calc
        _ = (q.c ^ 2 + q.s ^ 2) * (r.c * dx + r.s * dy) := by
          dsimp [c, s, normalDot, normalCross]; ring
        _ = _ := by rw [q.unit_normal, one_mul]
    dsimp [U, X, Y]
    rw [← he]
    ring
  have hV : V = -s * X + c * Y := by
    have he : -s * (q.c * dx + q.s * dy) + c * (-q.s * dx + q.c * dy) =
        -r.s * dx + r.c * dy := by
      calc
        _ = (q.c ^ 2 + q.s ^ 2) * (-r.s * dx + r.c * dy) := by
          dsimp [c, s, normalDot, normalCross]; ring
        _ = _ := by rw [q.unit_normal, one_mul]
    dsimp [V, X, Y]
    rw [← he]
    ring
  have hRq : pairRadius q r = f * (1 + |c| + |s|) := by
    dsimp [pairRadius, f, c, s]
    rw [← hside]
    ring
  have hRr : pairRadius r q = f * (1 + |c| + |s|) := by
    have hdot : normalDot r q = c := by dsimp [normalDot, c]; ring
    have hcross : normalCross r q = -s := by dsimp [normalCross, s]; ring
    dsimp [pairRadius]
    rw [hdot, hcross, abs_neg, ← hside]
    dsimp [f]
    ring
  by_contra hn
  have hbounds :
      |q.c * dx + q.s * dy| < f * (1 + |c| + |s|) ∧
      |-q.s * dx + q.c * dy| < f * (1 + |c| + |s|) ∧
      |r.c * dx + r.s * dy| < f * (1 + |c| + |s|) ∧
      |-r.s * dx + r.c * dy| < f * (1 + |c| + |s|) := by
    change ¬ (pairRadius q r ≤ |q.c * dx + q.s * dy| ∨
      pairRadius q r ≤ |-q.s * dx + q.c * dy| ∨
      pairRadius r q ≤ |r.c * dx + r.s * dy| ∨
      pairRadius r q ≤ |-r.s * dx + r.c * dy|) at hn
    rw [hRq, hRr] at hn
    simpa only [not_or, not_le] using hn
  have normalize (v : ℝ) (hv : |v| < f * (1 + |c| + |s|)) :
      |v / f| < 1 + |c| + |s| := by
    rw [abs_div, abs_of_pos hf]
    apply (div_lt_iff₀ hf).mpr
    nlinarith only [hv]
  obtain ⟨x, y, hx, hy, hru, hrv⟩ := SATSigned.overlap c s X Y U V hunit hU hV
    (normalize _ hbounds.1) (normalize _ hbounds.2.1)
    (normalize _ hbounds.2.2.1) (normalize _ hbounds.2.2.2)
  let px := centerX q + f * (q.c * x - q.s * y)
  let py := centerY q + f * (q.s * x + q.c * y)
  have hqu : q.c * (px - centerX q) + q.s * (py - centerY q) = f * x := by
    calc
      _ = f * x * (q.c ^ 2 + q.s ^ 2) := by dsimp [px, py]; ring
      _ = f * x := by rw [q.unit_normal, mul_one]
  have hqv : -q.s * (px - centerX q) + q.c * (py - centerY q) = f * y := by
    calc
      _ = f * y * (q.c ^ 2 + q.s ^ 2) := by dsimp [px, py]; ring
      _ = f * y := by rw [q.unit_normal, mul_one]
  have hfU : f * U = r.c * dx + r.s * dy := by
    dsimp [U]
    field_simp [ne_of_gt hf]
  have hfV : f * V = -r.s * dx + r.c * dy := by
    dsimp [V]
    field_simp [ne_of_gt hf]
  have hru' : r.c * (px - centerX r) + r.s * (py - centerY r) =
      f * (c * x + s * y - U) := by
    calc
      _ = f * (c * x + s * y) - (r.c * dx + r.s * dy) := by
        dsimp [px, py, c, s, normalDot, normalCross, dx, dy]; ring
      _ = _ := by rw [← hfU]; ring
  have hrv' : -r.s * (px - centerX r) + r.c * (py - centerY r) =
      f * (-s * x + c * y - V) := by
    calc
      _ = f * (-s * x + c * y) - (-r.s * dx + r.c * dy) := by
        dsimp [px, py, c, s, normalDot, normalCross, dx, dy]; ring
      _ = _ := by rw [← hfV]; ring
  have scale (z : ℝ) (hz : |z| < 1) : -f < f * z ∧ f * z < f := by
    obtain ⟨hl, hu⟩ := abs_lt.mp hz
    have hl' := mul_lt_mul_of_pos_left hl hf
    have hu' := mul_lt_mul_of_pos_left hu hf
    constructor <;> nlinarith only [hl', hu']
  apply hd px py
  constructor
  · apply (inside_centered_iff q px py).mpr
    rw [hqu, hqv]
    have hx' := scale x hx
    have hy' := scale y hy
    dsimp [InBands]
    dsimp [f] at hx' hy' ⊢
    exact ⟨by linarith only [hx'.1], by linarith only [hx'.2],
      by linarith only [hy'.1], by linarith only [hy'.2]⟩
  · apply (inside_centered_iff r px py).mpr
    rw [hru', hrv', ← hside]
    have hx' := scale (c * x + s * y - U) hru
    have hy' := scale (-s * x + c * y - V) hrv
    dsimp [InBands]
    dsimp [f] at hx' hy' ⊢
    exact ⟨by linarith only [hx'.1], by linarith only [hx'.2],
      by linarith only [hy'.1], by linarith only [hy'.2]⟩

end N12Compact.CongruentSAT
