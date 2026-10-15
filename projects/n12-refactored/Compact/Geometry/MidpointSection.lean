import Compact.Geometry.ClosedFrames
import Compact.Geometry.SectionCapacity

/-! A unit vertical span forces a unit horizontal segment at its midpoint.
Both owned endpoints are strict. This is essential: closed endpoints alone
can give a section of exactly one at a diagonal corner. The proof covers the
whole orientation circle and does not divide by a normal component. -/
namespace N12Compact.MidpointSection

open S12 S12Pilot
set_option Elab.async false

/-- A closed unit segment all of whose points lie in the strict interior. -/
def UnitSection (q : OpenSquare) (h : ℝ) : Prop :=
  ∃ z : ℝ, ∀ d : ℝ, |d| ≤ 1/2 → q.Inside (z+d) h

private theorem positive_height_bounds (q : OpenSquare) (x y : ℝ)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (hp : q.Inside x y) :
    -q.side*(q.c+q.s)/2 < y-centerY q ∧
      y-centerY q < q.side*(q.c+q.s)/2 := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (inside_centered_iff q x y).mp hp
  have identity :
      q.s*(q.c*(x-centerX q)+q.s*(y-centerY q)) +
      q.c*(-q.s*(x-centerX q)+q.c*(y-centerY q)) = y-centerY q := by
    calc
      _ = (q.c^2+q.s^2)*(y-centerY q) := by ring
      _ = _ := by rw [q.unit_normal, one_mul]
  have u₀ := mul_le_mul_of_nonneg_left h₀.le hs
  have u₁ := mul_le_mul_of_nonneg_left h₁.le hs
  have v₀ := mul_lt_mul_of_pos_left h₂ hc
  have v₁ := mul_lt_mul_of_pos_left h₃ hc
  constructor <;> nlinarith only [identity,u₀,u₁,v₀,v₁]

/-- Exact continuous unit-segment radius for the actual side length. -/
theorem scalar_unit_section (a c s t : ℝ) (ha : 1 < a)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (cut : 2*|t| < a*(c+s)-2*c*s) :
    ∃ z : ℝ, ∀ d : ℝ, |d| ≤ 1/2 →
      InBands (-a/2) (-a/2) a
        (c*(z+d)+s*t) (-s*(z+d)+c*t) := by
  have hc1 : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
  have hs1 : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  let D := a*(c+s)-2*c*s
  have hD : 0 < D := by dsimp [D]; linarith only [cut,abs_nonneg t]
  let lam := t/D
  have hld : lam*D=t := div_mul_cancel₀ t (ne_of_gt hD)
  have hl : |lam| < 1/2 := by
    dsimp [lam]
    rw [abs_div,abs_of_pos hD]
    apply (div_lt_iff₀ hD).mpr
    dsimp [D]
    linarith only [cut]
  let U := (a-c)*lam
  let V := (a-s)*lam
  have hu : |U| < (a-c)/2 := by
    dsimp [U]
    rw [abs_mul,abs_of_pos (show 0<a-c by linarith only [ha,hc1])]
    have h := mul_lt_mul_of_pos_left hl (show 0<a-c by linarith only [ha,hc1])
    linarith only [h]
  have hv : |V| < (a-s)/2 := by
    dsimp [V]
    rw [abs_mul,abs_of_pos (show 0<a-s by linarith only [ha,hs1])]
    have h := mul_lt_mul_of_pos_left hl (show 0<a-s by linarith only [ha,hs1])
    linarith only [h]
  have hUV : s*U+c*V=t := by
    calc
      _ = lam*D := by dsimp [U,V,D]; ring
      _ = t := hld
  let z := c*U-s*V
  have first : c*z+s*t=U := by
    calc
      _ = (c^2+s^2)*U := by rw [← hUV]; dsimp [z]; ring
      _ = U := by rw [unit,one_mul]
  have second : -s*z+c*t=V := by
    calc
      _ = (c^2+s^2)*V := by rw [← hUV]; dsimp [z]; ring
      _ = V := by rw [unit,one_mul]
  refine ⟨z,?_⟩
  intro d hd
  have cd : |c*d| ≤ c/2 := by
    rw [abs_mul,abs_of_nonneg hc]
    have h := mul_le_mul_of_nonneg_left hd hc
    linarith only [h]
  have sd : |s*d| ≤ s/2 := by
    rw [abs_mul,abs_of_nonneg hs]
    have h := mul_le_mul_of_nonneg_left hd hs
    linarith only [h]
  have Ustrict : |U+c*d| < a/2 := by
    have h := abs_add U (c*d)
    linarith only [h,hu,cd]
  have Vstrict : |V-s*d| < a/2 := by
    have h : |V-s*d| ≤ |V|+|s*d| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add V (-(s*d))
    linarith only [h,hv,sd]
  have eU : c*(z+d)+s*t=U+c*d := by
    calc
      _ = (c*z+s*t)+c*d := by ring
      _ = _ := by rw [first]
  have eV : -s*(z+d)+c*t=V-s*d := by
    calc
      _ = (-s*z+c*t)-s*d := by ring
      _ = _ := by rw [second]
  rw [eU,eV]
  obtain ⟨loU,hiU⟩ := abs_lt.mp Ustrict
  obtain ⟨loV,hiV⟩ := abs_lt.mp Vstrict
  exact ⟨by linarith only [loU],by linarith only [hiU],
    by linarith only [loV],by linarith only [hiV]⟩

/-- More generally, a vertical span d suffices whenever d≥2cs in a positive
frame. No numerical angle partition or global upper side bound is needed. -/
theorem positive_span (q : OpenSquare) (x₀ x₁ h d : ℝ)
    (ha : 1 < q.side) (hc : 0 < q.c) (hs : 0 ≤ q.s)
    (p₀ : q.Inside x₀ (h-d/2)) (p₁ : q.Inside x₁ (h+d/2))
    (span : 2*q.c*q.s ≤ d) : UnitSection q h := by
  have low := (positive_height_bounds q x₀ (h-d/2) hc hs p₀).1
  have high := (positive_height_bounds q x₁ (h+d/2) hc hs p₁).2
  have cut : 2*|h-centerY q| < q.side*(q.c+q.s)-2*q.c*q.s := by
    have bound : |h-centerY q| < (q.side*(q.c+q.s)-d)/2 := by
      apply abs_lt.mpr
      constructor <;> linarith only [low,high]
    linarith only [bound,span]
  obtain ⟨z,hz⟩ := scalar_unit_section q.side q.c q.s (h-centerY q)
    ha hc.le hs q.unit_normal cut
  refine ⟨centerX q+z,?_⟩
  intro u hu
  apply (inside_centered_iff q ((centerX q+z)+u) h).mpr
  have hx : ((centerX q+z)+u)-centerX q=z+u := by ring
  rw [hx]
  exact hz u hu

/-- Uniform all-orientation form: the two actual owned heights differ by one. -/
theorem of_unit_span (q : OpenSquare) (x₀ x₁ h : ℝ) (ha : 1 < q.side)
    (p₀ : q.Inside x₀ (h-1/2)) (p₁ : q.Inside x₁ (h+1/2)) : UnitSection q h := by
  obtain ⟨r,hc,hs,hside,hi,_⟩ := ClosedFrames.positive_frame q
  have span : 2*r.c*r.s ≤ (1:ℝ) := by
    nlinarith only [r.unit_normal,sq_nonneg (r.c-r.s)]
  obtain ⟨z,hz⟩ := positive_span r x₀ x₁ h 1
    (by simpa only [hside] using ha) hc hs ((hi _ _).mpr p₀) ((hi _ _).mpr p₁) span
  exact ⟨z,fun d hd => (hi _ _).mp (hz d hd)⟩

/-- A strict interior unit segment in the container hits one of its three
interior integer slots, including equality at either segment endpoint. -/
theorem grid_hit (q : OpenSquare) (h : ℝ) (box : InsideContainer q)
    (hsection : UnitSection q h) : ∃ j : Fin 3, q.Inside ((j.val:ℝ)+1) h := by
  obtain ⟨z,hz⟩ := hsection
  have lo : 0 ≤ z-1/2 := by
    have hp := (box _ _ (hz (-1/2) (by norm_num [abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)]))).1
    linarith only [hp]
  have up : z+1/2 ≤ 4 := (box _ _ (hz (1/2) (by rw [abs_of_nonneg (by norm_num)]))).2.1
  have point (k : ℝ) (hlo : z-1/2 ≤ k) (hhi : k ≤ z+1/2) : q.Inside k h := by
    have h := hz (k-z) (abs_le.mpr ⟨by linarith,by linarith⟩)
    convert h using 1 <;> ring
  by_cases h₁ : z-1/2 ≤ 1
  · refine ⟨0,?_⟩
    norm_num
    exact point 1 h₁ (by linarith only [lo])
  by_cases h₂ : z-1/2 ≤ 2
  · refine ⟨1,?_⟩
    norm_num
    exact point 2 h₂ (by linarith only [h₁])
  · refine ⟨2,?_⟩
    norm_num
    exact point 3 (by linarith only [up]) (by linarith only [h₂])

#print axioms of_unit_span
#print axioms grid_hit
end N12Compact.MidpointSection
