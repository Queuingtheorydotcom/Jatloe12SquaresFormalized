import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Algebraic wall-chain summation, independent of angle parameterization.

There are `n + 1` centers and `n` edges. Each edge's separating normal is
selected from its two squares; its signed transverse component is `b i`.
This module proves the summation argument from explicit local separation,
wall-support, and common-height hypotheses. It does NOT establish the
separating-axis theorem or certify those hypotheses for a packing.

Source assembled without a fresh Lean replay. No admission or new axiom is
used. See the accompanying C977 audit for the actual validation boundary.
-/

namespace N12Compact.WallChain

open scoped BigOperators

def variation (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, |s (i + 1) - s i|

def transverseLoss (b y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, b i * (y (i + 1) - y i)

private theorem product_le_abs_width (v d h : ℝ) (hd : |d| ≤ h) :
    v * d ≤ |v| * h := by
  calc
    v * d ≤ |v * d| := le_abs_self _
    _ = |v| * |d| := abs_mul _ _
    _ ≤ |v| * h := mul_le_mul_of_nonneg_left hd (abs_nonneg v)

theorem height_distance (lower h u v : ℝ)
    (hu : lower ≤ u ∧ u ≤ lower + h)
    (hv : lower ≤ v ∧ v ≤ lower + h) : |u - v| ≤ h := by
  apply abs_le.mpr
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- The selected-normal loss is paid by one height displacement, rather than
adding independent losses for every pair in a chain. -/
theorem selected_edge_loss (s t b y z base h : ℝ)
    (hb : b = s ∨ b = t)
    (hy : |y - base| ≤ h) (hz : |z - base| ≤ h) :
    b * (z - y) - (t * (z - base) - s * (y - base)) ≤
      h * |t - s| := by
  rcases hb with hb | hb
  · rw [hb]
    calc
      s * (z - y) - (t * (z - base) - s * (y - base)) =
          (s - t) * (z - base) := by ring
      _ ≤ |s - t| * h := product_le_abs_width _ _ _ hz
      _ = h * |t - s| := by rw [abs_sub_comm]; ring
  · rw [hb]
    calc
      t * (z - y) - (t * (z - base) - s * (y - base)) =
          (s - t) * (y - base) := by ring
      _ ≤ |s - t| * h := product_le_abs_width _ _ _ hy
      _ = h * |t - s| := by rw [abs_sub_comm]; ring

/-- Discrete integration by parts using the endpoint potential
`s i * (y i - y 0)`. No trigonometric estimate or selection enumeration. -/
theorem selected_loss_le (n : ℕ) (s b y : ℕ → ℝ) (h : ℝ)
    (hselect : ∀ i, i < n → b i = s i ∨ b i = s (i + 1))
    (hheight : ∀ i, i ≤ n → |y i - y 0| ≤ h) :
    transverseLoss b y n ≤ h * (|s n| + variation s n) := by
  have step : ∀ m,
      (∀ i, i < m → b i = s i ∨ b i = s (i + 1)) →
      (∀ i, i ≤ m → |y i - y 0| ≤ h) →
      transverseLoss b y m ≤ s m * (y m - y 0) + h * variation s m := by
    intro m
    induction m with
    | zero =>
        intro _ _
        simp [transverseLoss, variation]
    | succ m ih =>
        intro hs hy
        have hp := ih
          (fun i hi => hs i (Nat.lt_trans hi (Nat.lt_succ_self m)))
          (fun i hi => hy i (Nat.le_trans hi (Nat.le_succ m)))
        have he := selected_edge_loss (s m) (s (m + 1)) (b m)
          (y m) (y (m + 1)) (y 0) h
          (hs m (Nat.lt_succ_self m))
          (hy m (Nat.le_succ m)) (hy (m + 1) (Nat.le_refl _))
        simp only [transverseLoss, variation, Finset.sum_range_succ] at hp ⊢
        linarith
  have hp := step n hselect hheight
  have hend := product_le_abs_width (s n) (y n - y 0) h
    (hheight n (Nat.le_refl _))
  nlinarith

/-- Local pair support inequalities sum to a center displacement. -/
theorem pair_sum (n : ℕ) (x y s b : ℕ → ℝ) (a k : ℝ)
    (hpair : ∀ i, i < n →
      a + a * k * |s (i + 1) - s i| - b i * (y (i + 1) - y i) ≤
        x (i + 1) - x i) :
    (n : ℝ) * a + a * k * variation s n - transverseLoss b y n ≤
      x n - x 0 := by
  have step : ∀ m,
      (∀ i, i < m →
        a + a * k * |s (i + 1) - s i| - b i * (y (i + 1) - y i) ≤
          x (i + 1) - x i) →
      (m : ℝ) * a + a * k * variation s m - transverseLoss b y m ≤
        x m - x 0 := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [variation, transverseLoss]
    | succ m ih =>
        intro hp
        have hprev := ih (fun i hi => hp i (Nat.lt_trans hi (Nat.lt_succ_self m)))
        have hedge := hp m (Nat.lt_succ_self m)
        simp only [variation, transverseLoss, Finset.sum_range_succ,
          Nat.cast_succ, Nat.cast_add, Nat.cast_one] at hprev ⊢
        nlinarith
  exact step n hpair

/-- A right wall and a chain of `n+1` squares force its first center strictly
left of `width-(n+1/2)`. True side length `a>1` supplies all strictness.

The local inequalities are deliberately hypotheses: proving a SAT bridge
and certifying geometric enclosures are independent obligations. -/
theorem first_center_cut (n : ℕ) (x y s b : ℕ → ℝ)
    (a k lower h width : ℝ)
    (ha : 1 < a) (hk : 0 ≤ k) (hh : h ≤ k)
    (hselect : ∀ i, i < n → b i = s i ∨ b i = s (i + 1))
    (hheight : ∀ i, i ≤ n → lower ≤ y i ∧ y i ≤ lower + h)
    (hpair : ∀ i, i < n →
      a + a * k * |s (i + 1) - s i| - b i * (y (i + 1) - y i) ≤
        x (i + 1) - x i)
    (hwall : a / 2 + a * k * |s n| ≤ width - x n) :
    x 0 < width - ((n : ℝ) + 1 / 2) := by
  have hdist : ∀ i, i ≤ n → |y i - y 0| ≤ h := by
    intro i hi
    exact height_distance lower h (y i) (y 0)
      (hheight i hi) (hheight 0 (Nat.zero_le n))
  have ht := selected_loss_le n s b y h hselect hdist
  have hp := pair_sum n x y s b a k hpair
  have hv : 0 ≤ variation s n := by
    unfold variation
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hgain : 0 ≤ a * k - h := by
    have hprod := mul_nonneg (show 0 ≤ a - 1 by linarith) hk
    nlinarith
  have hpaid := mul_nonneg hgain (add_nonneg (abs_nonneg (s n)) hv)
  have hstrict := mul_pos (show 0 < (n : ℝ) + 1 / 2 by linarith)
    (show 0 < a - 1 by linarith)
  nlinarith

end N12Compact.WallChain
