import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
The scalar core of the positive border endpoint argument. Unlike a long-chord
argument for the target, it proves that the target reaches past `t + a`.

This is a theorem about real inequalities, not a replacement packing model.
The packing bridge must derive the upper-face inequality from actual owned
points and failure to own `(t,1)`, and the bottom inequality from containment.
It must also supply the orientation and center bounds. No case exclusion is
claimed here. This source has not yet been compiled.
-/

namespace N12Compact.BorderEndpoint

/-- Exact uniform test-row bounds for the entire rational half-angle band,
including its upper endpoint. The zero-sine endpoint is handled separately
by rectangle membership in the original-model bridge. -/
theorem half_angle_band (z : ℝ) (hz : 0 < z) (hzmax : z ≤ 2 / 7) :
    let c := (1 - z ^ 2) / (1 + z ^ 2)
    let s := 2 * z / (1 + z ^ 2)
    0 < c ∧ 0 < s ∧ s ≤ c ∧ c * c + s * s = 1 ∧
      (c + s - 1) / c < (45 / 98 : ℝ) ∧
      (45 / 98 : ℝ) ≤ c / (1 + c) ∧ (45 / 98 : ℝ) < 1 / 2 := by
  let c := (1 - z ^ 2) / (1 + z ^ 2)
  let s := 2 * z / (1 + z ^ 2)
  have hden : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have hzsq : z ^ 2 ≤ 4 / 49 := by
    have hp := mul_nonneg (sub_nonneg.mpr hzmax)
      (show 0 ≤ (2 / 7 : ℝ) + z by linarith only [hz])
    nlinarith only [hp]
  have hc : 0 < c :=
    div_pos (by nlinarith only [hzsq] : 0 < 1 - z ^ 2) hden
  have hs : 0 < s := div_pos (by linarith only [hz] : 0 < 2 * z) hden
  have hsc : s ≤ c := by
    apply (div_le_div_iff_of_pos_right hden).mpr
    nlinarith only [hzmax, hzsq]
  have hcden : c * (1 + z ^ 2) = 1 - z ^ 2 := by
    dsimp [c]
    field_simp [hden.ne']
  have hsden : s * (1 + z ^ 2) = 2 * z := by
    dsimp [s]
    field_simp [hden.ne']
  have hunit : c * c + s * s = 1 := by
    dsimp [c, s]
    field_simp [hden.ne']
    <;> ring
  have hcos : (45 / 53 : ℝ) ≤ c := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hzsq]
  have hlo : (c + s - 1) / c < (45 / 98 : ℝ) := by
    apply (div_lt_iff₀ hc).mpr
    apply (mul_lt_mul_left hden).mp
    have hp := mul_pos
      (show 0 < 1 - z by linarith only [hzmax])
      (show 0 < 45 - 151 * z by linarith only [hzmax])
    nlinarith only [hcden, hsden, hp]
  have hhi : (45 / 98 : ℝ) ≤ c / (1 + c) := by
    apply (le_div_iff₀ (by linarith only [hc] : 0 < 1 + c)).mpr
    linarith only [hcos]
  exact ⟨hc, hs, hsc, hunit, hlo, hhi, by norm_num⟩

/-- A scalar endpoint obstruction valid throughout a closed orientation band.
For `c = (1-z²)/(1+z²)`, `s = 2z/(1+z²)`, `0 < z ≤ 2/7`, take
`h = 45/98`: `(c+s-1)/c ≤ 4/9 < h ≤ c/(1+c)`.

The three displayed expressions are the lower longitudinal endpoint and the
two upper endpoint candidates on the row `y=h`. Both the center abscissa `X`
and `t+a` lie strictly inside that row interval. In particular, a target
long-chord premise is unnecessary. Equality in either geometric input bound
is retained; strictness comes from `a > 1`.
-/
theorem positive_endpoints (a c s X Y t h : ℝ)
    (ha : 1 < a) (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c)
    (hunit : c * c + s * s = 1)
    (hlo : (c + s - 1) / c < h) (hhi : h ≤ c / (1 + c))
    (hhalf : h < 1 / 2) (hX : X ≤ t + 1)
    (hface : a / 2 ≤ s * (X - t) + c * (1 - Y))
    (hwall : a * (c + s) / 2 ≤ Y) :
    let l := X + (s * (Y - h) - a / 2) / c
    let ru := l + a / c
    let rv := X + (c * (h - Y) + a / 2) / s
    h < Y ∧ t < l ∧ l < X ∧ X < t + a ∧ t + a < ru ∧ t + a < rv := by
  let E := s * (X - t) + c * (1 - Y) - a / 2
  let W := Y - a * (c + s) / 2
  have ha0 : 0 < a := by linarith only [ha]
  have hE : 0 ≤ E := by dsimp [E]; linarith only [hface]
  have hW : 0 ≤ W := by dsimp [W]; linarith only [hwall]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg (c - 1)]
  have hs1 : s < 1 := by
    nlinarith [sq_nonneg (s - 1), mul_pos hc hc]
  have hsum : 1 ≤ c + s := by
    have h0 := mul_nonneg hc.le (sub_nonneg.mpr hc1)
    have h1 := mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
    nlinarith only [hunit, h0, h1]
  have hcs : 1 ≤ c * (c + s) := by
    have hh := mul_nonneg hs.le (sub_nonneg.mpr hsc)
    nlinarith only [hunit, hh]
  have hss : s * (c + s) ≤ 1 := by
    have hh := mul_nonneg hc.le (sub_nonneg.mpr hsc)
    nlinarith only [hunit, hh]
  have hlow : c + s - 1 < h * c := (div_lt_iff₀ hc).mp hlo
  have hhigh : h * (1 + c) ≤ c :=
    (le_div_iff₀ (by linarith only [hc] : 0 < 1 + c)).mp hhi
  have hslack : E + c * W =
      s * (X - t) + c - a * (1 + c * (c + s)) / 2 := by
    dsimp [E, W]
    ring
  have hproduct := mul_nonneg ha0.le (sub_nonneg.mpr hcs)
  have hbound : 1 < a * (1 + c * (c + s)) / 2 := by
    nlinarith only [hproduct, ha]
  have hdelta : s * (X - t) ≤ s := by
    calc
      s * (X - t) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [hX]) hs.le
      _ = s := mul_one s
  have hWrow : W < h := by
    apply (mul_lt_mul_left hc).mp
    calc
      c * W ≤ E + c * W := le_add_of_nonneg_left hE
      _ = s * (X - t) + c - a * (1 + c * (c + s)) / 2 := hslack
      _ ≤ s + c - a * (1 + c * (c + s)) / 2 := by linarith only [hdelta]
      _ < c + s - 1 := by linarith only [hbound]
      _ < c * h := by simpa only [mul_comm] using hlow
  have hheight : h < Y := by
    have hp := mul_nonneg ha0.le (sub_nonneg.mpr hsum)
    nlinarith only [hp, hwall, ha, hhalf]
  have hcenter : s * (Y - h) < a / 2 := by
    have hp := mul_nonneg ha0.le (sub_nonneg.mpr hss)
    have hw := mul_lt_mul_of_pos_left hWrow hs
    dsimp [W] at hw
    nlinarith only [hp, hw]
  have hmargin : c * a - c * c - h * (s * s) > 0 := by
    have hp := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hhigh)
    have ha' := mul_pos hc (sub_pos.mpr ha)
    calc
      0 < c * (a - 1) + (1 - c) * (c - h * (1 + c)) :=
        add_pos_of_pos_of_nonneg ha' hp
      _ = c * a - c * c - h * (s * s) + h * (c * c + s * s - 1) := by ring
      _ = c * a - c * c - h * (s * s) := by rw [hunit]; ring
  let L := c * (X - t) + s * (Y - h) - a / 2
  have hidentity : s * L = c * a - c * c - h * (s * s) + c * E + W := by
    calc
      s * L = c * a - c * c - h * (s * s) + c * E + W +
          Y * (c * c + s * s - 1) := by dsimp [L, E, W]; ring
      _ = c * a - c * c - h * (s * s) + c * E + W := by rw [hunit]; ring
  have hL : 0 < L := by
    have he := mul_nonneg hc.le hE
    have hp : 0 < s * L := by nlinarith only [hidentity, hmargin, he, hW]
    exact (mul_pos_iff_of_pos_left hs).mp hp
  have hlower : t - X < (s * (Y - h) - a / 2) / c := by
    apply (lt_div_iff₀ hc).mpr
    dsimp [L] at hL
    nlinarith only [hL]
  have hupper : (s * (Y - h) - a / 2) / c < 0 := by
    apply (div_lt_iff₀ hc).mpr
    nlinarith only [hcenter]
  have hwidth : a ≤ a / c := by
    apply (le_div_iff₀ hc).mpr
    have hp := mul_nonneg ha0.le (sub_nonneg.mpr hc1)
    nlinarith only [hp]
  have hrv : t + a - X < (c * (h - Y) + a / 2) / s := by
    apply (lt_div_iff₀ hs).mpr
    have hp := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hs1)
    dsimp [E] at hE
    nlinarith only [hp, hE, hlow]
  dsimp
  exact ⟨hheight, by linarith only [hlower], by linarith only [hupper],
    by linarith only [hX, ha], by linarith only [hlower, hwidth],
    by linarith only [hrv]⟩

/-- The endpoint inequalities imply the four actual strict square bands.
The conclusion can be fed directly to the original model's
`inside_centered_iff`; no new notion of packing is introduced. -/
theorem inside_bands_of_endpoints (a c s X Y h x : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    (hY : h < Y) (hX : X ≤ x)
    (hl : X + (s * (Y - h) - a / 2) / c < x)
    (hu : x < X + (s * (Y - h) - a / 2) / c + a / c)
    (hv : x < X + (c * (h - Y) + a / 2) / s) :
    -a / 2 < c * (x - X) + s * (h - Y) ∧
      c * (x - X) + s * (h - Y) < a / 2 ∧
    -a / 2 < -s * (x - X) + c * (h - Y) ∧
      -s * (x - X) + c * (h - Y) < a / 2 := by
  have hl' : (s * (Y - h) - a / 2) / c < x - X := by
    linarith only [hl]
  have hlo := (div_lt_iff₀ hc).mp hl'
  have hsum : (s * (Y - h) - a / 2) / c + a / c =
      (s * (Y - h) + a / 2) / c := by
    rw [← add_div]
    congr 1
    ring
  have hu' : x - X < (s * (Y - h) + a / 2) / c := by
    linarith only [hu, hsum]
  have hupper := (lt_div_iff₀ hc).mp hu'
  have hv' : x - X < (c * (h - Y) + a / 2) / s := by
    linarith only [hv]
  have hbottom := (lt_div_iff₀ hs).mp hv'
  have hxnonnegative := mul_nonneg hs.le (sub_nonneg.mpr hX)
  have hypositive := mul_pos hc (sub_pos.mpr hY)
  exact ⟨by nlinarith only [hlo], by nlinarith only [hupper],
    by nlinarith only [hbottom], by nlinarith only [hxnonnegative, hypositive, ha]⟩

/-- Once actual disjoint row sections put one long follower after the target,
the case `t=2` is impossible. The interval-order and containment hypotheses
must be obtained from the original squares, not guessed from a trace. -/
theorem one_follower_impossible (a t l r : ℝ) (ha : 1 < a) (ht : 2 ≤ t)
    (hstart : t + a ≤ l) (hwidth : 1 < r - l) (hend : r ≤ 4) : False := by
  linarith

/-- The analogous terminal for two followers, used at `t=1`. -/
theorem two_followers_impossible (a t l₁ r₁ l₂ r₂ : ℝ)
    (ha : 1 < a) (ht : 1 ≤ t) (hstart : t + a ≤ l₁)
    (hwidth₁ : 1 < r₁ - l₁) (horder : r₁ ≤ l₂)
    (hwidth₂ : 1 < r₂ - l₂) (hend : r₂ ≤ 4) : False := by
  linarith

end N12Compact.BorderEndpoint
