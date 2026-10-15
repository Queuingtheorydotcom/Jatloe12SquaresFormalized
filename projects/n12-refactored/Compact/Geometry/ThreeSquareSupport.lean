import Compact.Geometry.FourSquareAnchors
import Compact.Geometry.SectionCapacity

/-! Support and section facts for the original OpenSquare. These replace
the missing legacy closed-support/long-chord imports in the terminal proof.
They do not certify a radius bound or an entry enclosure. -/
namespace N12Compact.ThreeSquare
open S12 S12Pilot FourSquareAnchors SectionCapacity

noncomputable def supportRadius (q : OpenSquare) (nx ny : ℝ) : ℝ :=
  q.side / 2 * (|nx * q.c + ny * q.s| + |-nx * q.s + ny * q.c|)

theorem closed_coordinates (q : OpenSquare) (x y : ℝ)
    (hp : ClosedInside q x y) :
    |q.c * (x - centerX q) + q.s * (y - centerY q)| ≤ q.side / 2 ∧
    |-q.s * (x - centerX q) + q.c * (y - centerY q)| ≤ q.side / 2 := by
  have hc := center_coordinates q
  constructor <;> apply abs_le.mpr <;> constructor <;>
    dsimp [ClosedInside] at hp <;> nlinarith [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hc.1, hc.2]

theorem closed_support (q : OpenSquare) (x y nx ny : ℝ)
    (hp : ClosedInside q x y) :
    |nx * (x - centerX q) + ny * (y - centerY q)| ≤ supportRadius q nx ny := by
  let u := q.c * (x - centerX q) + q.s * (y - centerY q)
  let v := -q.s * (x - centerX q) + q.c * (y - centerY q)
  let A := nx * q.c + ny * q.s
  let B := -nx * q.s + ny * q.c
  have hb := closed_coordinates q x y hp
  have hu : |u| ≤ q.side / 2 := hb.1
  have hv : |v| ≤ q.side / 2 := hb.2
  have he : nx * (x - centerX q) + ny * (y - centerY q) = A * u + B * v := by
    calc
      _ = (q.c ^ 2 + q.s ^ 2) * (nx * (x - centerX q) + ny * (y - centerY q)) := by
        rw [q.unit_normal, one_mul]
      _ = _ := by dsimp [A, B, u, v]; ring
  calc
    _ = |A * u + B * v| := congrArg abs he
    _ ≤ |A * u| + |B * v| := abs_add _ _
    _ = |A| * |u| + |B| * |v| := by rw [abs_mul, abs_mul]
    _ ≤ |A| * (q.side / 2) + |B| * (q.side / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg A))
        (mul_le_mul_of_nonneg_left hv (abs_nonneg B))
    _ = supportRadius q nx ny := by dsimp [A, B, supportRadius]; ring

theorem inside_support (q : OpenSquare) (x y nx ny : ℝ) (hp : q.Inside x y) :
    |nx * (x - centerX q) + ny * (y - centerY q)| ≤ supportRadius q nx ny := by
  apply closed_support q x y nx ny
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩

theorem bottom_wall (q : OpenSquare) (hc : 0 ≤ q.c) (box : InsideContainer q) :
    q.side * (q.c + |q.s|) / 2 ≤ centerY q := by
  have hw : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y :=
    fun x y hp => ⟨(box x y hp).1, (box x y hp).2.2.1⟩
  by_cases hs : 0 ≤ q.s
  · simpa only [abs_of_nonneg hs] using (positive_frame_wall_bounds q hc hs hw).2
  · have ht : ∀ x y, (turnFrame q).Inside x y → 0 ≤ x ∧ 0 ≤ y := by
      intro x y hp
      exact hw x y ((turnFrame_inside q x y).mp hp)
    have bound := (positive_frame_wall_bounds (turnFrame q)
      (by dsimp [turnFrame]; linarith) hc ht).2
    rw [turnFrame_centerY] at bound
    simp only [turnFrame, abs_of_nonpos (le_of_not_ge hs)]
    dsimp [turnFrame] at bound
    linarith

/-- The original normalization cap makes every horizontal half-width less
than one. It does not require a near-horizontal orientation. -/
theorem half_width_lt_one (q : OpenSquare) (cap : q.side ≤ 1001 / 1000) :
    supportRadius q 1 0 < 1 := by
  have hc := abs_nonneg q.c
  have hs := abs_nonneg q.s
  have sum : |q.c| + |q.s| ≤ 3 / 2 := by
    nlinarith [q.unit_normal, sq_abs q.c, sq_abs q.s, sq_nonneg (|q.c| - |q.s|)]
  have bound := mul_le_mul cap sum (add_nonneg hc hs) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
  simp only [supportRadius, one_mul, zero_mul, add_zero, neg_mul, zero_add, abs_neg]
  nlinarith only [bound]

/-- Any certified section longer than one crosses the center abscissa.
The proof closes the endpoints of its open interval by affine limits. -/
theorem section_crosses_center (q : OpenSquare) (h l u : ℝ)
    (cap : q.side ≤ 1001 / 1000) (long : 1 < u - l)
    (inside : ∀ x, l < x → x < u → q.Inside x h) :
    l < centerX q ∧ centerX q < u := by
  let w := supportRadius q 1 0
  have hw : w < 1 := half_width_lt_one q cap
  have point (x : ℝ) (hl : l < x) (hu : x < u) :
      centerX q - w ≤ x ∧ x ≤ centerX q + w := by
    have hp := inside_support q x h 1 0 (inside x hl hu)
    simp only [one_mul, zero_mul, add_zero] at hp
    have hb := abs_le.mp hp
    constructor <;> dsimp [w] <;> linarith [hb.1, hb.2]
  have hl : centerX q - w ≤ l := by
    have bound : 0 ≤ l - centerX q + w := by
      apply affine_endpoint_nonnegative (u - l) 1 (l - centerX q + w) (by linarith)
      intro t ht0 ht1
      have hp := (point (l + t) (by linarith) (by linarith)).1
      linarith only [hp]
    linarith only [bound]
  have hu : u ≤ centerX q + w := by
    have bound : 0 ≤ centerX q + w - u := by
      apply affine_endpoint_nonnegative (u - l) 1 (centerX q + w - u) (by linarith)
      intro t ht0 ht1
      have hp := (point (u - t) (by linarith) (by linarith)).2
      linarith only [hp]
    linarith only [bound]
  constructor <;> linarith

theorem intervals_ordered (l u l' u' : ℝ) (hu : l < u) (hu' : l' < u')
    (apart : ∀ x, ¬ (l < x ∧ x < u ∧ l' < x ∧ x < u')) :
    u ≤ l' ∨ u' ≤ l := by
  by_cases h : u ≤ l'
  · exact Or.inl h
  · right
    by_contra h'
    have gap : max l l' < min u u' := by
      apply max_lt_iff.mpr
      exact ⟨lt_min hu (lt_of_not_ge h'), lt_min (lt_of_not_ge h) hu'⟩
    let x := (max l l' + min u u') / 2
    have hlo : max l l' < x := by dsimp [x]; linarith only [gap]
    have hhi : x < min u u' := by dsimp [x]; linarith only [gap]
    exact apart x ⟨lt_of_le_of_lt (le_max_left _ _) hlo,
      lt_of_lt_of_le hhi (min_le_left _ _), lt_of_le_of_lt (le_max_right _ _) hlo,
      lt_of_lt_of_le hhi (min_le_right _ _)⟩

theorem ordered_sections (q r : OpenSquare) (h l u l' u' : ℝ)
    (hu : l < u) (hu' : l' < u')
    (sq : ∀ x, l < x → x < u → q.Inside x h)
    (sr : ∀ x, l' < x → x < u' → r.Inside x h)
    (cross : l < u')
    (apart : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y)) : u ≤ l' := by
  rcases intervals_ordered l u l' u' hu hu' (by
    intro x hx
    exact apart x h ⟨sq x hx.1 hx.2.1, sr x hx.2.2.1 hx.2.2.2⟩) with yes | no
  · exact yes
  · exact False.elim ((not_le_of_gt cross) no)

theorem section_right_wall (q : OpenSquare) (h l u : ℝ) (hu : l < u)
    (sq : ∀ x, l < x → x < u → q.Inside x h) (box : InsideContainer q) : u ≤ 4 := by
  have bound : 0 ≤ 4 - u := by
    apply affine_endpoint_nonnegative (u - l) 1 (4 - u) (by linarith)
    intro t ht0 ht1
    have hp := (box (u - t) h (sq _ (by linarith) (by linarith))).2.1
    linarith only [hp]
  linarith only [bound]

end N12Compact.ThreeSquare
