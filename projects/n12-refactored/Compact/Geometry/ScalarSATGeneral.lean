import Compact.Geometry.ScalarSATIntervals

/-! Elementary separating-axis overlap for squares with independent positive
half-side lengths. The proof intersects open intervals twice; no separation
functional or compactness theorem is used. -/
namespace N12Compact.SATGeneral
noncomputable section
set_option Elab.async false
open SATIntervals

def Overlap (a b c s U V : ℝ) : Prop :=
  ∃ x y : ℝ, |x| < a ∧ |y| < a ∧
    |c*x+s*y-U| < b ∧ |-s*x+c*y-V| < b

/-- One-dimensional open intervals overlap exactly under the strict distance bound. -/
theorem interval_overlap (a b X : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hX : |X| < a+b) : ∃ x : ℝ, |x| < a ∧ |x-X| < b := by
  rcases abs_lt.mp hX with ⟨hXm,hXp⟩
  obtain ⟨x,hl,hu⟩ := between_three (-a) (X-b) (X-b) a (X+b) (X+b)
    (by exact ⟨by linarith, by linarith, by linarith⟩)
    (by exact ⟨by linarith, by linarith, by linarith⟩)
    (by exact ⟨by linarith, by linarith, by linarith⟩)
  exact ⟨x, abs_lt.mpr ⟨hl.1,hu.1⟩,
    abs_lt.mpr ⟨by linarith [hl.2.1], by linarith [hu.2.1]⟩⟩

/-- Fourier–Motzkin elimination leaves four mutually overlapping y intervals. -/
theorem positive_y_intervals (a b c s X Y U V : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hU : U=c*X+s*Y) (hV : V= -s*X+c*Y)
    (hX : |X| < a+b*(c+s)) (hY : |Y| < a+b*(c+s))
    (hUB : |U| < b+a*(c+s)) (hVB : |V| < b+a*(c+s)) :
    ∃ y, (-a < y ∧ (U-b-c*a)/s < y ∧ (V-b-s*a)/c < y ∧ Y-b*(c+s) < y) ∧
      (y < a ∧ y < (U+b+c*a)/s ∧ y < (V+b+s*a)/c ∧ y < Y+b*(c+s)) := by
  have hXi : c*U-s*V=X := by
    calc
      _ = X*(c^2+s^2) := by rw [hU,hV]; ring
      _ = X := by rw [hunit,mul_one]
  have hau : a*(c^2+s^2)=a := by rw [hunit,mul_one]
  have hbu : b*(c^2+s^2)=b := by rw [hunit,mul_one]
  have hbsq := mul_nonneg hb.le (sq_nonneg s)
  have hbcq := mul_nonneg hb.le (sq_nonneg c)
  have hbsum := mul_pos hb (show 0 < c+s by linarith)
  have hca := mul_pos hc ha
  have hsa := mul_pos hs ha
  rcases abs_lt.mp hX with ⟨hXm,hXp⟩
  rcases abs_lt.mp hY with ⟨hYm,hYp⟩
  rcases abs_lt.mp hUB with ⟨hUm,hUp⟩
  rcases abs_lt.mp hVB with ⟨hVm,hVp⟩
  have hcXm := mul_lt_mul_of_pos_left hXm hc
  have hcXp := mul_lt_mul_of_pos_left hXp hc
  have hsXm := mul_lt_mul_of_pos_left hXm hs
  have hsXp := mul_lt_mul_of_pos_left hXp hs
  apply between_four
  · refine ⟨by linarith, ?_, ?_, by linarith only [hYm]⟩
    · apply (lt_div_iff₀ hs).2; nlinarith only [hUm]
    · apply (lt_div_iff₀ hc).2; nlinarith only [hVm]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hs).2; nlinarith only [hUp]
    · apply (div_lt_div_iff_of_pos_right hs).2; nlinarith only [hb,hca]
    · apply (div_lt_div_iff₀ hs hc).2; nlinarith only [hXi,hXp,hau]
    · apply (div_lt_iff₀ hs).2; nlinarith only [hcXp,hU,hbu,hbsq]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hc).2; nlinarith only [hVp]
    · apply (div_lt_div_iff₀ hc hs).2; nlinarith only [hXi,hXm,hau]
    · apply (div_lt_div_iff_of_pos_right hc).2; nlinarith only [hb,hsa]
    · apply (div_lt_iff₀ hc).2; nlinarith only [hsXm,hV,hbu,hbcq]
  · refine ⟨by linarith only [hYp], ?_, ?_, by linarith only [hbsum]⟩
    · apply (lt_div_iff₀ hs).2; nlinarith only [hcXm,hU,hbu,hbsq]
    · apply (lt_div_iff₀ hc).2; nlinarith only [hsXp,hV,hbu,hbcq]

theorem positive_overlap (a b c s X Y U V : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hU : U=c*X+s*Y) (hV : V= -s*X+c*Y)
    (hX : |X| < a+b*(c+s)) (hY : |Y| < a+b*(c+s))
    (hUB : |U| < b+a*(c+s)) (hVB : |V| < b+a*(c+s)) :
    Overlap a b c s U V := by
  obtain ⟨y,hl,hu⟩ := positive_y_intervals a b c s X Y U V
    ha hb hc hs hunit hU hV hX hY hUB hVB
  have hYi : s*U+c*V=Y := by
    calc
      _ = Y*(c^2+s^2) := by rw [hU,hV]; ring
      _ = Y := by rw [hunit,mul_one]
  have hyunit : y*(c^2+s^2)=y := by rw [hunit,mul_one]
  have hylU := (div_lt_iff₀ hs).1 hl.2.1
  have hyuU := (lt_div_iff₀ hs).1 hu.2.1
  have hylV := (div_lt_iff₀ hc).1 hl.2.2.1
  have hyuV := (lt_div_iff₀ hc).1 hu.2.2.1
  have h₀ : -a < a ∧ -a < (U+b-s*y)/c ∧ -a < (c*y-V+b)/s := by
    refine ⟨by linarith, ?_, ?_⟩
    · apply (lt_div_iff₀ hc).2; nlinarith only [hyuU]
    · apply (lt_div_iff₀ hs).2; nlinarith only [hylV]
  have h₁ : (U-b-s*y)/c < a ∧ (U-b-s*y)/c < (U+b-s*y)/c ∧
      (U-b-s*y)/c < (c*y-V+b)/s := by
    refine ⟨?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hc).2; nlinarith only [hylU]
    · apply (div_lt_div_iff_of_pos_right hc).2; linarith only [hb]
    · apply (div_lt_div_iff₀ hc hs).2; nlinarith only [hYi,hyunit,hl.2.2.2]
  have h₂ : (c*y-V-b)/s < a ∧ (c*y-V-b)/s < (U+b-s*y)/c ∧
      (c*y-V-b)/s < (c*y-V+b)/s := by
    refine ⟨?_, ?_, ?_⟩
    · apply (div_lt_iff₀ hs).2; nlinarith only [hyuV]
    · apply (div_lt_div_iff₀ hs hc).2; nlinarith only [hYi,hyunit,hu.2.2.2]
    · apply (div_lt_div_iff_of_pos_right hs).2; linarith only [hb]
  obtain ⟨x,hxl,hxu⟩ := between_three _ _ _ _ _ _ h₀ h₁ h₂
  refine ⟨x,y,abs_lt.mpr ⟨hxl.1,hxu.1⟩,abs_lt.mpr ⟨hl.1,hu.1⟩,?_,?_⟩
  · have hlo := (div_lt_iff₀ hc).1 hxl.2.1
    have hhi := (lt_div_iff₀ hc).1 hxu.2.1
    apply abs_lt.mpr; constructor <;> linarith only [hlo,hhi]
  · have hlo := (div_lt_iff₀ hs).1 hxl.2.2
    have hhi := (lt_div_iff₀ hs).1 hxu.2.2
    apply abs_lt.mpr; constructor <;> linarith only [hlo,hhi]

theorem nonnegative_overlap (a b c s X Y U V : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (hU : U=c*X+s*Y) (hV : V= -s*X+c*Y)
    (hX : |X| < a+b*(c+s)) (hY : |Y| < a+b*(c+s))
    (hUB : |U| < b+a*(c+s)) (hVB : |V| < b+a*(c+s)) :
    Overlap a b c s U V := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hc' : c=0 := hc0.symm
    have hs' : s=1 := by nlinarith [hunit]
    subst c; subst s
    obtain ⟨x,hx,hxX⟩ := interval_overlap a b X ha hb (by simpa using hX)
    obtain ⟨y,hy,hyY⟩ := interval_overlap a b Y ha hb (by simpa using hY)
    refine ⟨x,y,hx,hy,?_,?_⟩
    · have hU' : U=Y := by simpa using hU
      simpa [hU'] using hyY
    · have hV' : V= -X := by simpa using hV
      have he : -(1:ℝ)*x+0*y-V= -(x-X) := by rw [hV']; ring
      simpa only [he,abs_neg] using hxX
  · rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hs' : s=0 := hs0.symm
      have hc' : c=1 := by nlinarith [hunit]
      subst s; subst c
      obtain ⟨x,hx,hxX⟩ := interval_overlap a b X ha hb (by simpa using hX)
      obtain ⟨y,hy,hyY⟩ := interval_overlap a b Y ha hb (by simpa using hY)
      refine ⟨x,y,hx,hy,?_,?_⟩
      · have hU' : U=X := by simpa using hU
        simpa [hU'] using hxX
      · have hV' : V=Y := by simpa using hV
        simpa [hV'] using hyY
    · exact positive_overlap a b c s X Y U V ha hb hcpos hspos hunit hU hV hX hY hUB hVB

theorem flip_s (a b c s U V : ℝ)
    (h : Overlap a b c (-s) U (-V)) : Overlap a b c s U V := by
  obtain ⟨x,y,hx,hy,hU,hV⟩ := h
  refine ⟨x,-y,hx,by simpa only [abs_neg] using hy,?_,?_⟩
  · simpa only [mul_neg,neg_mul] using hU
  · have he : -s*x+c*(-y)-V= -(-(-s)*x+c*y-(-V)) := by ring
    rw [he,abs_neg]
    exact hV

theorem flip_c (a b c s U V : ℝ)
    (h : Overlap a b (-c) s U (-V)) : Overlap a b c s U V := by
  obtain ⟨x,y,hx,hy,hU,hV⟩ := h
  refine ⟨-x,y,by simpa only [abs_neg] using hx,hy,?_,?_⟩
  · simpa only [mul_neg,neg_mul] using hU
  · have he : -s*(-x)+c*y-V= -(-s*x+(-c)*y-(-V)) := by ring
    rw [he,abs_neg]
    exact hV

theorem nonneg_c_overlap (a b c s X Y U V : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hunit : c^2+s^2=1) (hU : U=c*X+s*Y) (hV : V= -s*X+c*Y)
    (hX : |X| < a+b*(|c|+|s|)) (hY : |Y| < a+b*(|c|+|s|))
    (hUB : |U| < b+a*(|c|+|s|)) (hVB : |V| < b+a*(|c|+|s|)) :
    Overlap a b c s U V := by
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hc,abs_of_nonneg hs] at hX hY hUB hVB
    exact nonnegative_overlap a b c s X Y U V ha hb hc hs hunit hU hV hX hY hUB hVB
  · have hsneg : s < 0 := lt_of_not_ge hs
    rw [abs_of_nonneg hc,abs_of_neg hsneg] at hX hY hUB hVB
    apply flip_s
    exact nonnegative_overlap a b c (-s) X (-Y) U (-V) ha hb hc (by linarith)
      (by simpa only [neg_sq] using hunit)
      (by nlinarith only [hU]) (by nlinarith only [hV])
      hX (by simpa only [abs_neg] using hY) hUB (by simpa only [abs_neg] using hVB)

/-- Absence of separation in the four edge directions produces an interior
intersection for arbitrary rotations and arbitrary positive half-side lengths. -/
theorem overlap (a b c s X Y U V : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hunit : c^2+s^2=1) (hU : U=c*X+s*Y) (hV : V= -s*X+c*Y)
    (hX : |X| < a+b*(|c|+|s|)) (hY : |Y| < a+b*(|c|+|s|))
    (hUB : |U| < b+a*(|c|+|s|)) (hVB : |V| < b+a*(|c|+|s|)) :
    Overlap a b c s U V := by
  by_cases hc : 0 ≤ c
  · exact nonneg_c_overlap a b c s X Y U V ha hb hc hunit hU hV hX hY hUB hVB
  · have hcneg : c < 0 := lt_of_not_ge hc
    apply flip_c
    exact nonneg_c_overlap a b (-c) s (-X) Y U (-V) ha hb (by linarith)
      (by simpa only [neg_sq] using hunit)
      (by nlinarith only [hU]) (by nlinarith only [hV])
      (by simpa only [abs_neg] using hX) (by simpa only [abs_neg] using hY)
      (by simpa only [abs_neg] using hUB) (by simpa only [abs_neg] using hVB)

end
end N12Compact.SATGeneral
