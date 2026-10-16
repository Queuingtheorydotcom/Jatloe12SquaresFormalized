import Compact.Geometry.SectionCapacity
import S12.WallGeometry

/-!
# A long horizontal section for every orientation

The original square model is unchanged. A square of side `a > 1` has a
horizontal section of length `(a+1)/2 > 1` whenever the cut is within
`(|c|+|s|-2|c*s|)/2` of its center height.

The proof constructs the midpoint of a unit horizontal segment in the closed
unit reference square, then uses the actual larger side for strict room. It
does not divide by either frame component, so axis-aligned squares require no
special case. There is no angle grid, maximum-angle choice, or numerical data.
-/

namespace N12Compact.LongSectionGeometry

open S12 S12Pilot SectionCapacity

noncomputable def sectionRadius (q : OpenSquare) : ℝ :=
  (|q.c| + |q.s| - 2 * |q.c * q.s|) / 2

@[simp] theorem sectionRadius_turnFrame (q : OpenSquare) :
    sectionRadius (turnFrame q) = sectionRadius q := by
  simp [sectionRadius, turnFrame, abs_mul, add_comm, mul_comm]

/-- Positive frame reindexing preserves the section radius as well as the
actual square and its center. This is not a spatial symmetry assumption. -/
theorem positive_frame_radius (q : OpenSquare) :
    ∃ r : OpenSquare, 0 ≤ r.c ∧ 0 ≤ r.s ∧ r.side = q.side ∧
      centerY r = centerY q ∧ sectionRadius r = sectionRadius q ∧
      ∀ x y, r.Inside x y ↔ q.Inside x y := by
  by_cases hc : 0 ≤ q.c
  · by_cases hs : 0 ≤ q.s
    · exact ⟨q, hc, hs, rfl, rfl, rfl, by intros; rfl⟩
    · refine ⟨turnFrame q, ?_, ?_, by simp, by simp, by simp, by simp⟩
      · dsimp [turnFrame]
        linarith
      · exact hc
  · by_cases hs : 0 ≤ q.s
    · refine ⟨turnFrame (turnFrame (turnFrame q)), ?_, ?_,
        by simp, by simp, by simp, by simp⟩ <;>
        dsimp [turnFrame] <;> linarith
    · refine ⟨turnFrame (turnFrame q), ?_, ?_,
        by simp, by simp, by simp, by simp⟩ <;>
        dsimp [turnFrame] <;> linarith

/-- Construct the midpoint and prove all four open face inequalities for
an entire interval. All inequalities include the extreme allowed cut height. -/
theorem scalar_long_section (a c s t : ℝ) (ha : 1 < a)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (unit : c ^ 2 + s ^ 2 = 1)
    (cut : |t| ≤ (c + s - 2 * c * s) / 2) :
    ∃ z : ℝ, ∀ d : ℝ, |d| < (a + 1) / 4 →
      InBands (-a / 2) (-a / 2) a
        (c * (z + d) + s * t) (-s * (z + d) + c * t) := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg (c - 1)]
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg (s - 1)]
  have hsum : 1 ≤ c + s := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1),
      mul_nonneg hs (sub_nonneg.mpr hs1)]
  have hprod : 2 * c * s ≤ 1 := by nlinarith [sq_nonneg (c - s)]
  let D := c + s - 2 * c * s
  have hD : 0 < D := by
    by_contra h
    have hd : c + s - 2 * c * s ≤ 0 := le_of_not_gt h
    have he : c + s = 1 := by linarith
    have he2 := congrArg (fun x : ℝ => x ^ 2) he
    nlinarith only [he, he2, unit, hd]
  let lam := t / D
  have hlamD : lam * D = t := by
    exact div_mul_cancel₀ t (ne_of_gt hD)
  have hlam : |lam| ≤ 1 / 2 := by
    dsimp [lam]
    rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    linarith only [cut]
  let U := (1 - c) * lam
  let V := (1 - s) * lam
  have hU : |U| ≤ (1 - c) / 2 := by
    dsimp [U]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1)]
    nlinarith only [mul_le_mul_of_nonneg_left hlam (sub_nonneg.mpr hc1)]
  have hV : |V| ≤ (1 - s) / 2 := by
    dsimp [V]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1)]
    nlinarith only [mul_le_mul_of_nonneg_left hlam (sub_nonneg.mpr hs1)]
  have hUV : s * U + c * V = t := by
    calc
      s * U + c * V = lam * D := by dsimp [U, V, D]; ring
      _ = t := hlamD
  let z := c * U - s * V
  have hfirst : c * z + s * t = U := by
    calc
      c * z + s * t = (c ^ 2 + s ^ 2) * U := by
        rw [← hUV]
        dsimp [z]
        ring
      _ = U := by rw [unit, one_mul]
  have hsecond : -s * z + c * t = V := by
    calc
      -s * z + c * t = (c ^ 2 + s ^ 2) * V := by
        rw [← hUV]
        dsimp [z]
        ring
      _ = V := by rw [unit, one_mul]
  have margin (v : ℝ) (hv : v ≤ 1) :
      (1 - v) / 2 + v * ((a + 1) / 4) < a / 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ a - 1 by linarith)
    nlinarith only [ha, hp]
  refine ⟨z, ?_⟩
  intro d hd
  have hcd : |c * d| ≤ c * ((a + 1) / 4) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hd.le hc
  have hsd : |s * d| ≤ s * ((a + 1) / 4) := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hd.le hs
  have habsFirst : |U + c * d| < a / 2 := by
    calc
      |U + c * d| ≤ |U| + |c * d| := abs_add_le _ _
      _ ≤ (1 - c) / 2 + c * ((a + 1) / 4) := add_le_add hU hcd
      _ < a / 2 := margin c hc1
  have habsSecond : |V - s * d| < a / 2 := by
    calc
      |V - s * d| = |V + -(s * d)| := rfl
      _ ≤ |V| + |-(s * d)| := abs_add_le _ _
      _ = |V| + |s * d| := by rw [abs_neg]
      _ ≤ (1 - s) / 2 + s * ((a + 1) / 4) := add_le_add hV hsd
      _ < a / 2 := margin s hs1
  have heFirst : c * (z + d) + s * t = U + c * d := by
    calc
      c * (z + d) + s * t = (c * z + s * t) + c * d := by ring
      _ = U + c * d := by rw [hfirst]
  have heSecond : -s * (z + d) + c * t = V - s * d := by
    calc
      -s * (z + d) + c * t = (-s * z + c * t) - s * d := by ring
      _ = V - s * d := by rw [hsecond]
  rw [heFirst, heSecond]
  obtain ⟨hlU, huU⟩ := abs_lt.mp habsFirst
  obtain ⟨hlV, huV⟩ := abs_lt.mp habsSecond
  dsimp [InBands]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem positive_frame_long_section (q : OpenSquare) (h : ℝ)
    (ha : 1 < q.side) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (cut : |h - centerY q| ≤ (q.c + q.s - 2 * q.c * q.s) / 2) :
    LongSection q h := by
  obtain ⟨z, hz⟩ := scalar_long_section q.side q.c q.s (h - centerY q)
    ha hc hs q.unit_normal cut
  refine ⟨centerX q + z - (q.side + 1) / 4,
    centerX q + z + (q.side + 1) / 4, ?_, ?_⟩
  · linarith
  · intro x hl hu
    have hd : |x - (centerX q + z)| < (q.side + 1) / 4 := by
      apply abs_lt.mpr
      constructor <;> linarith
    apply (inside_centered_iff q x h).mpr
    have he : x - centerX q = z + (x - (centerX q + z)) := by ring
    rw [he]
    exact hz (x - (centerX q + z)) hd

/-- Unconditional geometric bridge from the exact radius bound to a genuine
open horizontal section. Arbitrary orientations and radius equalities remain
included. Only the side hypothesis supplies strictness. -/
theorem horizontal_long_section (q : OpenSquare) (h : ℝ)
    (ha : 1 < q.side) (cut : |h - centerY q| ≤ sectionRadius q) :
    LongSection q h := by
  obtain ⟨r, hc, hs, hside, hY, hrad, hinside⟩ := positive_frame_radius q
  have hcut : |h - centerY r| ≤ (r.c + r.s - 2 * r.c * r.s) / 2 := by
    rw [← hrad, ← hY] at cut
    simpa only [sectionRadius, abs_mul, abs_of_nonneg hc, abs_of_nonneg hs,
      mul_assoc] using cut
  obtain ⟨l, u, hwidth, hsegment⟩ := positive_frame_long_section r h
    (by simpa only [hside] using ha) hc hs hcut
  exact ⟨l, u, hwidth, fun x hl hu => (hinside x h).mp (hsegment x hl hu)⟩

#print axioms horizontal_long_section

end N12Compact.LongSectionGeometry
