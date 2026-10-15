import Compact.Geometry.LongSection
import S12.OrientedCoverage
import Mathlib.Tactic.FinCases

/-!
# Whole-angle long vertical sections and a shared three-neighbor window

The radius data have the same meaning as the historical angle chord
certificates. Their soundness now uses the compact, already proved all-angle
long-section construction and the three-point capacity argument.
-/

namespace N12Compact.AngleSection

open S12 S12Pilot LongSectionGeometry SectionCapacity

structure Radius where
  sumUpper : ℚ
  radius : ℚ

def Radius.Check (w : Radius) (angle : AngleEnclosure) : Prop :=
  0 ≤ w.radius ∧ 2 * w.radius ≤ 1 + w.sumUpper - w.sumUpper ^ 2 ∧
  ((supportQuadratic 1 0 w.sumUpper 1 1).CheckOn angle.lower angle.upper ∨
    (0 ≤ w.sumUpper ∧ 2 ≤ w.sumUpper ^ 2))

instance (w : Radius) (angle : AngleEnclosure) : Decidable (w.Check angle) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Radius.bound (w : Radius) (angle : {a : AngleEnclosure // a.Check})
    (checked : w.Check angle.val) (t : ℝ)
    (ht0 : (angle.val.lower : ℝ) ≤ t) (ht1 : t ≤ (angle.val.upper : ℝ)) :
    (w.radius : ℝ) ≤ (normalC t + normalS t - 2 * normalC t * normalS t) / 2 := by
  have hlo : (0 : ℝ) ≤ angle.val.lower := by exact_mod_cast angle.property.1
  have hhi : (angle.val.upper : ℝ) ≤ 1 := by exact_mod_cast angle.property.2.1
  obtain ⟨hc, hs⟩ := normal_nonnegative t (le_trans hlo ht0) (le_trans ht1 hhi)
  have hu := normal_unit t
  have hB : normalC t + normalS t ≤ (w.sumUpper : ℝ) := by
    rcases checked.2.2 with h | h
    · have hh := supportQuadratic_sound 1 0 w.sumUpper 1 1 _ _ h t ht0 ht1
      simpa using hh
    · have hB0 : (0 : ℝ) ≤ w.sumUpper := by exact_mod_cast h.1
      have hB2 : (2 : ℝ) ≤ (w.sumUpper : ℝ) ^ 2 := by exact_mod_cast h.2
      nlinarith [sq_nonneg (normalC t - normalS t)]
  have hc1 : normalC t ≤ 1 := by
    nlinarith [sq_nonneg (normalS t), sq_nonneg (normalC t - 1)]
  have hs1 : normalS t ≤ 1 := by
    nlinarith [sq_nonneg (normalC t), sq_nonneg (normalS t - 1)]
  have hsum : 1 ≤ normalC t + normalS t := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1),
      mul_nonneg hs (sub_nonneg.mpr hs1)]
  have hp := mul_nonneg (sub_nonneg.mpr hB)
    (show (0 : ℝ) ≤ w.sumUpper + normalC t + normalS t - 1 by linarith)
  have hr : 2 * (w.radius : ℝ) ≤ 1 + (w.sumUpper : ℝ) - (w.sumUpper : ℝ) ^ 2 := by
    exact_mod_cast checked.2.1
  nlinarith only [hu, hp, hr]

def VerticalSection (q : OpenSquare) (x : ℝ) : Prop :=
  ∃ l u : ℝ, 1 < u - l ∧ ∀ y, l < y → y < u → q.Inside x y

@[simp] theorem sectionRadius_swap (q : OpenSquare) :
    sectionRadius (pullSwap q) = sectionRadius q := by
  simp [sectionRadius, pullSwap, abs_mul, add_comm, mul_comm]

theorem oriented_vertical (leaf : PoseLeaf) (w : Radius)
    (checked : w.Check leaf.angle.val) (q : OpenSquare) (ha : 1 < q.side)
    (hq : leaf.AngleWitness q) (x : ℝ)
    (hx : |x - centerX q| ≤ (w.radius : ℝ)) : VerticalSection q x := by
  obtain ⟨r, t, hc, hs, ht0, ht1, hside, hX, hY, hin⟩ := hq
  have hlo : (0 : ℝ) ≤ leaf.angle.val.lower := by exact_mod_cast leaf.angle.property.1
  have hhi : (leaf.angle.val.upper : ℝ) ≤ 1 := by exact_mod_cast leaf.angle.property.2.1
  obtain ⟨hc0, hs0⟩ := normal_nonnegative t (le_trans hlo ht0) (le_trans ht1 hhi)
  have hr := w.bound leaf.angle checked t ht0 ht1
  have hdist : |x - centerY (pullSwap r)| ≤ sectionRadius (pullSwap r) := by
    rw [center_pullSwap_y, hX, sectionRadius_swap, sectionRadius, hc, hs,
      abs_of_nonneg hc0, abs_of_nonneg hs0, abs_mul,
      abs_of_nonneg hc0, abs_of_nonneg hs0]
    simpa only [mul_assoc] using le_trans hx hr
  obtain ⟨l, u, hlen, hseg⟩ := horizontal_long_section (pullSwap r) x
    (by change 1 < r.side; simpa only [hside] using ha) hdist
  exact ⟨l, u, hlen, fun y hy0 hy1 =>
    (hin x y).mp ((inside_pullSwap r y x).mp (hseg y hy0 hy1))⟩

theorem four_vertical_impossible (q : Fin 4 → OpenSquare) (x : ℝ)
    (hbox : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hsections : ∀ i, VerticalSection (q i) x) : False := by
  apply four_on_one_cut (fun i => pullSwap (q i)) x
    (fun i => container_pullSwap (q i) (hbox i))
  · intro i j hij y x h
    exact hd i j hij x y
      ⟨(inside_pullSwap (q i) y x).mp h.1, (inside_pullSwap (q j) y x).mp h.2⟩
  · intro i
    obtain ⟨l, u, hlen, hs⟩ := hsections i
    exact ⟨l, u, hlen, fun y hy0 hy1 => (inside_pullSwap (q i) y x).mpr (hs y hy0 hy1)⟩

theorem interval_nearby (lo hi y r : ℝ) (hr : 0 ≤ r) (hlh : lo ≤ hi)
    (hy0 : lo - r ≤ y) (hy1 : y ≤ hi + r) :
    ∃ h, lo ≤ h ∧ h ≤ hi ∧ |h - y| ≤ r := by
  refine ⟨max lo (y-r), le_max_left _ _, max_le hlh (by linarith), ?_⟩
  rw [abs_le]
  constructor
  · linarith [le_max_right lo (y-r)]
  · have hh : max lo (y-r) ≤ y+r := max_le (by linarith) (by linarith)
    linarith

/-- Three neighbor sections are shared by every source angle/pose in a
window. Only the source radius varies among the pruning plans. -/
theorem window_excludes (lo hi : ℝ) (ordered : lo ≤ hi)
    (q : Fin 4 → OpenSquare) (source : PoseLeaf) (radius : Radius)
    (checked : radius.Check source.angle.val)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (hs : source.OrientedRealizes (q 0))
    (neighbors : ∀ x, lo ≤ x → x ≤ hi → ∀ i : Fin 3,
      VerticalSection (q i.succ) x) :
    ¬ (lo - radius.radius ≤ centerX (q 0) ∧ centerX (q 0) ≤ hi + radius.radius) := by
  rintro ⟨hlo, hhi⟩
  obtain ⟨x, hx0, hx1, hx⟩ := interval_nearby lo hi (centerX (q 0)) radius.radius
    (by exact_mod_cast checked.1) ordered hlo hhi
  have h0 := oriented_vertical source radius checked (q 0) (ha 0) hs.2 x hx
  apply four_vertical_impossible q x hb hd
  intro i
  fin_cases i
  · exact h0
  · exact neighbors x hx0 hx1 0
  · exact neighbors x hx0 hx1 1
  · exact neighbors x hx0 hx1 2

#print axioms window_excludes
end N12Compact.AngleSection
