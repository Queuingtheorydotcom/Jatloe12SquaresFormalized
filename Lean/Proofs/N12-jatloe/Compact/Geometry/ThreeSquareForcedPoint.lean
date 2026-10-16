import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Analytic estimates for the three-square forced-point argument in
`s12-density-and-signs/EARLIER_THREE_SQUARE_PROOF.md`.

The original-square theorem is in `adapters/ThreeSquareOriginal.lean`.
It reuses the existing C709 endpoint and negative-transfer geometry, and
strengthens the archived statement: only the two followers need long
sections. The target needs its coarse height bound, not a long section.
No angle ordering, angle subdivision, or new certificate is used here.
-/
namespace N12Compact.ThreeSquare

/-- Every frame in the closed half-angle band `[-1/6,1/6]` has these
component bounds. Keeping the two component bounds as the interface lets
existing signed-frame and pose-cover theorems supply them directly. -/
def NearHorizontal (c s : ℝ) : Prop :=
  35 / 37 ≤ c ∧ |s| ≤ 12 / 37

/-- Rational half-angle parametrization supplies the whole closed band,
including zero and both endpoints, without enumerating angle bins. -/
theorem nearHorizontal_half_angle (z : ℝ) (hz : |z| ≤ 1 / 6) :
    NearHorizontal ((1 - z ^ 2) / (1 + z ^ 2))
      (2 * z / (1 + z ^ 2)) := by
  have hden : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have hz0 := abs_nonneg z
  have hzsq : z ^ 2 ≤ 1 / 36 := by
    have hh := mul_nonneg (sub_nonneg.mpr hz)
      (show 0 ≤ 1 / 6 + |z| by linarith)
    nlinarith [sq_abs z]
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith only [hzsq]
  · rw [abs_div, abs_of_pos hden, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ hden).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hz)
      (show 0 ≤ 6 - |z| by linarith)
    nlinarith [sq_abs z]

theorem cosine_bounds (c s : ℝ) (h : NearHorizontal c s)
    (unit : c ^ 2 + s ^ 2 = 1) : 0 < c ∧ c ≤ 1 := by
  constructor
  · linarith [h.1]
  · nlinarith [sq_nonneg s, h.1]

/-- The exact common row works throughout the whole orientation band. -/
theorem endpoint_band (c s : ℝ) (h : NearHorizontal c s)
    (unit : c ^ 2 + s ^ 2 = 1) :
    s ≤ c ∧ c + s - 1 ≤ c * (35 / 72) ∧
      (35 / 72) * (1 + c) ≤ c := by
  have hc := (cosine_bounds c s h unit).2
  have hs := (abs_le.mp h.2).2
  exact ⟨by linarith [h.1], by linarith [h.1], by linarith [h.1]⟩

/-- Three of the corner's four bands are automatic for a nonnegative
target angle. Only its upper face can exclude `(1,1)`. -/
theorem corner_nonnegative (a c s X Y : ℝ)
    (ha : 1 < a) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 12 / 37)
    (hX : 1 ≤ X ∧ X ≤ 3 / 2) (hY : 1 / 2 ≤ Y ∧ Y ≤ 1) :
    -a / 2 < c * (1 - X) + s * (1 - Y) ∧
    c * (1 - X) + s * (1 - Y) < a / 2 ∧
    -a / 2 < -s * (1 - X) + c * (1 - Y) := by
  have hcx0 := mul_nonneg hc (show 0 ≤ X - 1 by linarith [hX.1])
  have hcx1 : c * (X - 1) ≤ 1 / 2 := by
    have hh := mul_le_mul hc1 (show X - 1 ≤ 1 / 2 by linarith [hX.2])
      (show 0 ≤ X - 1 by linarith [hX.1]) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have hsy0 := mul_nonneg hs (show 0 ≤ 1 - Y by linarith [hY.2])
  have hsy1 : s * (1 - Y) ≤ 6 / 37 := by
    have hh := mul_le_mul hs1 (show 1 - Y ≤ 1 / 2 by linarith [hY.1])
      (show 0 ≤ 1 - Y by linarith [hY.2]) (by norm_num : (0 : ℝ) ≤ 12 / 37)
    nlinarith only [hh]
  have hsx0 := mul_nonneg hs (show 0 ≤ X - 1 by linarith [hX.1])
  have hcy0 := mul_nonneg hc (show 0 ≤ 1 - Y by linarith [hY.2])
  exact ⟨by nlinarith only [hcx1, hsy0, ha],
    by nlinarith only [hcx0, hsy1, ha],
    by nlinarith only [hsx0, hcy0, ha]⟩

/-- For a nonpositive target angle only the left face can exclude `(1,1)`.
The zero-angle case is included, with all inequalities still strict. -/
theorem corner_nonpositive (a c s X Y : ℝ)
    (ha : 1 < a) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hs : s ≤ 0) (hs1 : -s ≤ 12 / 37)
    (hX : 1 ≤ X ∧ X ≤ 3 / 2) (hY : 1 / 2 ≤ Y ∧ Y ≤ 1) :
    c * (1 - X) + s * (1 - Y) < a / 2 ∧
    -a / 2 < -s * (1 - X) + c * (1 - Y) ∧
    -s * (1 - X) + c * (1 - Y) < a / 2 := by
  have hcx0 := mul_nonneg hc (show 0 ≤ X - 1 by linarith [hX.1])
  have hsy0 := mul_nonpos_of_nonpos_of_nonneg hs
    (show 0 ≤ 1 - Y by linarith [hY.2])
  have hsx0 := mul_nonpos_of_nonpos_of_nonneg hs
    (show 0 ≤ X - 1 by linarith [hX.1])
  have hsx1 : (-s) * (X - 1) ≤ 6 / 37 := by
    have hh := mul_le_mul hs1 (show X - 1 ≤ 1 / 2 by linarith [hX.2])
      (show 0 ≤ X - 1 by linarith [hX.1]) (by norm_num : (0 : ℝ) ≤ 12 / 37)
    nlinarith only [hh]
  have hcy0 := mul_nonneg hc (show 0 ≤ 1 - Y by linarith [hY.2])
  have hcy1 : c * (1 - Y) ≤ 1 / 2 := by
    have hh := mul_le_mul hc1 (show 1 - Y ≤ 1 / 2 by linarith [hY.1])
      (show 0 ≤ 1 - Y by linarith [hY.2]) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  exact ⟨by nlinarith only [hcx0, hsy0, ha],
    by nlinarith only [hsx1, hcy0, ha],
    by nlinarith only [hsx0, hcy1, ha]⟩

/-- No vertical or backward face normal can separate the first two squares.
The vertical margin is `1 - 73/74 = 1/74`; a height of `1/2` suffices. -/
theorem projection_bounds (c s dx dy : ℝ)
    (h : NearHorizontal c s) (unit : c ^ 2 + s ^ 2 = 1)
    (hx : 1 / 2 ≤ dx ∧ dx ≤ 3 / 2) (hy : |dy| ≤ 1 / 2) :
    |-s * dx + c * dy| < 1 ∧ -1 < c * dx + s * dy := by
  have hc := cosine_bounds c s h unit
  have hx0 : 0 ≤ dx := by linarith [hx.1]
  have hsx : |s * dx| ≤ 18 / 37 := by
    rw [abs_mul, abs_of_nonneg hx0]
    have hh := mul_le_mul h.2 hx.2 hx0 (by norm_num : (0 : ℝ) ≤ 12 / 37)
    nlinarith only [hh]
  have hcy : |c * dy| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hc.1]
    have hh := mul_le_mul hc.2 hy (abs_nonneg dy) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have hsy : |s * dy| ≤ 6 / 37 := by
    rw [abs_mul]
    have hh := mul_le_mul h.2 hy (abs_nonneg dy) (by norm_num : (0 : ℝ) ≤ 12 / 37)
    nlinarith only [hh]
  have hcx := mul_nonneg hc.1.le hx0
  have ht := abs_add (-(s * dx)) (c * dy)
  rw [abs_neg] at ht
  have hd := neg_le_abs (s * dy)
  constructor
  · have he : -s * dx + c * dy = -(s * dx) + c * dy := by ring
    rw [he]
    linarith only [ht, hsx, hcy]
  · linarith only [hd, hsy, hcx]

/-- The relative-support hypotheses for the existing negative transfer
hold uniformly, without a comparison of the two angles. -/
theorem relative_bounds (c s C S k : ℝ)
    (h : NearHorizontal c s) (H : NearHorizontal C S)
    (unit : c ^ 2 + s ^ 2 = 1) (Unit : C ^ 2 + S ^ 2 = 1)
    (hk : C * k = c * S - s * C) : 0 ≤ c * C + s * S ∧ k ≤ 1 := by
  have hc := cosine_bounds c s h unit
  have hC := cosine_bounds C S H Unit
  have hcos : (35 / 37 : ℝ) ^ 2 ≤ c * C := by
    simpa only [pow_two] using mul_le_mul h.1 H.1 (by norm_num) hc.1.le
  have hsin : |s * S| ≤ (12 / 37 : ℝ) ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul h.2 H.2 (abs_nonneg S) (by norm_num)
  have hcS : |c * S| ≤ 12 / 37 := by
    rw [abs_mul, abs_of_pos hc.1]
    have hh := mul_le_mul hc.2 H.2 (abs_nonneg S) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  have hsC : |s * C| ≤ 12 / 37 := by
    rw [abs_mul, abs_of_pos hC.1]
    have hh := mul_le_mul h.2 hC.2 hC.1.le (by norm_num : (0 : ℝ) ≤ 12 / 37)
    simpa using hh
  constructor
  · linarith [neg_le_abs (s * S)]
  · apply (mul_le_mul_left hC.1).mp
    rw [hk, mul_one]
    linarith [le_abs_self (c * S), neg_le_abs (s * C), H.1]

/-- The archived target chord premise is only needed to recover this coarse
height interval. The stronger forced-point theorem does not use its chord. -/
theorem height_band (a c s Y : ℝ) (ha : 1 < a) (hc : 0 ≤ c)
    (unit : c ^ 2 + s ^ 2 = 1)
    (wall : a * (c + |s|) / 2 ≤ Y)
    (radius : Y - 35 / 72 ≤ (c + |s| - 2 * c * |s|) / 2) :
    1 / 2 < Y ∧ Y ≤ 71 / 72 := by
  have hb := abs_nonneg s
  have hu : c ^ 2 + |s| ^ 2 = 1 := by simpa using unit
  have hsum : 1 ≤ c + |s| := by nlinarith [mul_nonneg hc hb]
  have hwall := mul_le_mul_of_nonneg_left hsum (show 0 ≤ a by linarith)
  have hrad := mul_nonneg (show 0 ≤ c + |s| - 1 by linarith) (add_nonneg hc hb)
  constructor <;> nlinarith

end N12Compact.ThreeSquare
