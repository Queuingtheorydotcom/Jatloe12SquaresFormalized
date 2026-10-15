import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The polynomial inequalities in the continuous shallow-positive C1092 wall
argument. All variables range over real intervals; the coefficient estimates
below replace subdivision of the two angle triangles. Source awaiting the
deferred whole-project replay.
-/

namespace N12Compact.C1092ShallowPositiveScalars

theorem power_le_bound {z b : ℝ} (hz : 0 ≤ z) (hb : z ≤ b) (n : ℕ) :
    z ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hb hz (pow_nonneg (hz.trans hb) n)

def bottomQ (x z : ℝ) : ℝ :=
  (1 + z + z^2 + z^3) - x*(1 + z + 5*z^2 + z^3) +
    x^2*(z^3 - z^2 + 5*z - 1) + x^3*(z^3 - z^2 + z - 1)

def bottomB0 (z : ℝ) : ℝ := 3 - 22*z + 53*z^2 - 22*z^3
def bottomB1 (z : ℝ) : ℝ := 50 - 3*z + 94*z^2 + 47*z^3
def bottomB2 (z : ℝ) : ℝ := 47 - 94*z - 3*z^2 - 50*z^3
def bottomB3 (z : ℝ) : ℝ := 22 + 53*z + 22*z^2 + 3*z^3
def bottomP (x z : ℝ) : ℝ :=
  bottomB0 z + x*bottomB1 z + x^2*bottomB2 z + x^3*bottomB3 z

theorem bottomQ_lower (x z : ℝ) (hx : 0 ≤ x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z ≤ 1/2) : 47/256 ≤ bottomQ x z := by
  have hz2 : z^2 ≤ 1/4 := by
    have := power_le_bound hz hzmax 2
    norm_num at this ⊢
    exact this
  have hz3 : z^3 ≤ 1/8 := by
    have := power_le_bound hz hzmax 3
    norm_num at this ⊢
    exact this
  have hx2 : x^2 ≤ 1/16 := by
    have := power_le_bound hx hxmax 2
    norm_num at this ⊢
    exact this
  have hx3 : x^3 ≤ 1/64 := by
    have := power_le_bound hx hxmax 3
    norm_num at this ⊢
    exact this
  have hA : 1 ≤ 1 + z + z^2 + z^3 := by
    have hp : 0 ≤ z + z^2 + z^3 := by positivity
    linarith only [hp]
  have hB : 1 + z + 5*z^2 + z^3 ≤ 23/8 := by linarith only [hzmax, hz2, hz3]
  have hB0 : 0 ≤ 1 + z + 5*z^2 + z^3 := by positivity
  have hC : -5/4 ≤ z^3 - z^2 + 5*z - 1 := by
    nlinarith only [hz, hz2, pow_nonneg hz 3]
  have hD : -5/4 ≤ z^3 - z^2 + z - 1 := by
    nlinarith only [hz, hz2, pow_nonneg hz 3]
  have hXB := mul_le_mul hxmax hB hB0 (by norm_num : (0:ℝ) ≤ 1/4)
  have hXC := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hC)
  have hXD := mul_nonneg (pow_nonneg hx 3) (sub_nonneg.mpr hD)
  dsimp [bottomQ]
  nlinarith only [hA, hXB, hXC, hXD, hx2, hx3]

theorem bottom_coefficients (z : ℝ) (hz : 0 ≤ z) (hzmax : z ≤ 5/12) :
    63/263 ≤ bottomB0 z ∧ 195/4 ≤ bottomB1 z ∧
      3193/864 ≤ bottomB2 z ∧ 22 ≤ bottomB3 z := by
  have hz2 : z^2 ≤ 25/144 := by
    have := power_le_bound hz hzmax 2
    norm_num at this ⊢
    exact this
  have hz3 : z^3 ≤ 125/1728 := by
    have := power_le_bound hz hzmax 3
    norm_num at this ⊢
    exact this
  have hcube := mul_nonneg (sq_nonneg z)
    (show 0 ≤ 55/6 - 22*z by linarith only [hzmax])
  have hcomplete : bottomB0 z - ((263/6)*(z-66/263)^2 + 63/263) =
      z^2*(55/6 - 22*z) := by dsimp [bottomB0]; ring
  constructor
  · have hs := sq_nonneg (z-66/263)
    nlinarith only [hcomplete, hcube, hs]
  constructor
  · dsimp [bottomB1]
    nlinarith only [hzmax, sq_nonneg z, pow_nonneg hz 3]
  constructor
  · dsimp [bottomB2]
    linarith only [hzmax, hz2, hz3]
  · dsimp [bottomB3]
    have hp : 0 ≤ 53*z + 22*z^2 + 3*z^3 := by positivity
    linarith only [hp]

theorem bottomP_pos (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hzmax : z ≤ 5/12) : 0 < bottomP x z := by
  obtain ⟨h0, h1, h2, h3⟩ := bottom_coefficients z hz hzmax
  have hp1 := mul_nonneg hx (show 0 ≤ bottomB1 z by linarith only [h1])
  have hp2 := mul_nonneg (sq_nonneg x) (show 0 ≤ bottomB2 z by linarith only [h2])
  have hp3 := mul_nonneg (pow_nonneg hx 3) (show 0 ≤ bottomB3 z by linarith only [h3])
  dsimp [bottomP]
  linarith only [h0, hp1, hp2, hp3]

def ascendingC0 (x : ℝ) : ℝ := 2*x^2*(1+x^2)^4
def ascendingC1 (x : ℝ) : ℝ := 2*x*(1+x^2)^2*(5*x^4+7*x^2+4)
def ascendingC2 (x : ℝ) : ℝ := (1+x^2)*(20*x^6+34*x^4+x^3+25*x^2+x+3)
def ascendingC3 (x : ℝ) : ℝ := 20*x^7+38*x^5+5*x^4+32*x^3+6*x^2+6*x+1
def ascendingC4 (x : ℝ) : ℝ := 10*x^6+10*x^4+7*x^3+7*x^2+3*x-1
def ascendingC5 (x : ℝ) : ℝ := 2*x^5+3*x^2+1
def ascendingP (x ρ : ℝ) : ℝ :=
  ascendingC0 x + ascendingC1 x*ρ + ascendingC2 x*ρ^2 +
    ascendingC3 x*ρ^3 + ascendingC4 x*ρ^4 + ascendingC5 x*ρ^5

theorem ascending_coefficients (x : ℝ) (hx : 0 < x) :
    0 < ascendingC0 x ∧ 0 ≤ ascendingC1 x ∧ 0 ≤ ascendingC2 x ∧
      1 ≤ ascendingC3 x ∧ -1 ≤ ascendingC4 x ∧ 0 ≤ ascendingC5 x := by
  have hx0 := hx.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [ascendingC0]; positivity
  · dsimp [ascendingC1]; positivity
  · dsimp [ascendingC2]; positivity
  · have hp : 0 ≤ 20*x^7+38*x^5+5*x^4+32*x^3+6*x^2+6*x := by positivity
    dsimp [ascendingC3]; linarith only [hp]
  · have hp : 0 ≤ 10*x^6+10*x^4+7*x^3+7*x^2+3*x := by positivity
    dsimp [ascendingC4]; linarith only [hp]
  · dsimp [ascendingC5]; positivity

theorem ascendingP_pos (x ρ : ℝ) (hx : 0 < x)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 1) : 0 < ascendingP x ρ := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := ascending_coefficients x hx
  have hp1 := mul_nonneg h1 hρ
  have hp2 := mul_nonneg h2 (sq_nonneg ρ)
  have hp3 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hρ 3)
  have hp4 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hρ 4)
  have hp5 := mul_nonneg h5 (pow_nonneg hρ 5)
  have hpair := mul_nonneg (pow_nonneg hρ 3) (sub_nonneg.mpr hρmax)
  dsimp [ascendingP]
  nlinarith only [h0,hp1,hp2,hp3,hp4,hp5,hpair]

def descendingE0 (z : ℝ) : ℝ := 2*z^3*(1+z^2)^4
def descendingE1 (z : ℝ) : ℝ :=
  (1+z^2)^2*(12*z^6+3*z^5+16*z^4+3*z^3+z^2+1)
def descendingE2 (z : ℝ) : ℝ :=
  (1+z^2)*(30*z^7+15*z^6+51*z^5+21*z^4+14*z^3+5*z^2+z-1)
def descendingE3 (z : ℝ) : ℝ :=
  40*z^8+30*z^7+84*z^6+55*z^5+43*z^4+26*z^3+8*z^2+z+1
def descendingE4 (z : ℝ) : ℝ := 30*z^7+30*z^6+46*z^5+39*z^4+10*z^3+8*z^2+6*z-1
def descendingE5 (z : ℝ) : ℝ := (1+z)*(12*z^5+3*z^4+9*z^3+3*z^2-5*z+2)
def descendingE6 (z : ℝ) : ℝ := (1+z)*(1+z^2)*(2*z^2+z-2)
def descendingP (z ρ : ℝ) : ℝ :=
  descendingE0 z + descendingE1 z*ρ + descendingE2 z*ρ^2 +
    descendingE3 z*ρ^3 + descendingE4 z*ρ^4 +
    descendingE5 z*ρ^5 + descendingE6 z*ρ^6

theorem descending_coefficients (z : ℝ) (hz : 0 ≤ z) (hzmax : z ≤ 1/4) :
    0 ≤ descendingE0 z ∧ 1 ≤ descendingE1 z ∧ -17/16 ≤ descendingE2 z ∧
      0 ≤ descendingE3 z ∧ -1 ≤ descendingE4 z ∧
      0 < descendingE5 z ∧ -85/32 ≤ descendingE6 z := by
  have hz2 : z^2 ≤ 1/16 := by
    have := power_le_bound hz hzmax 2
    norm_num at this ⊢
    exact this
  have hfac : 0 ≤ 1+z^2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [descendingE0]; positivity
  · have h1 : (1:ℝ) ≤ (1+z^2)^2 := by nlinarith [sq_nonneg z, sq_nonneg (z^2)]
    have h2 : (1:ℝ) ≤ 12*z^6+3*z^5+16*z^4+3*z^3+z^2+1 := by
      have hp : 0 ≤ 12*z^6+3*z^5+16*z^4+3*z^3+z^2 := by positivity
      linarith only [hp]
    have hp := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (1+z^2))
    simpa only [one_mul, descendingE1] using hp
  · have hp : 0 ≤ (1+z^2)*(30*z^7+15*z^6+51*z^5+21*z^4+14*z^3+5*z^2+z) := by
      positivity
    dsimp [descendingE2]
    nlinarith only [hp, hz2]
  · dsimp [descendingE3]; positivity
  · have hp : 0 ≤ 30*z^7+30*z^6+46*z^5+39*z^4+10*z^3+8*z^2+6*z := by positivity
    dsimp [descendingE4]; linarith only [hp]
  · have hp : 0 ≤ 12*z^5+3*z^4+9*z^3+3*z^2 := by positivity
    have hi : 0 < 12*z^5+3*z^4+9*z^3+3*z^2-5*z+2 := by linarith only [hp, hzmax]
    dsimp [descendingE5]
    exact mul_pos (by linarith only [hz]) hi
  · have hu : (1+z)*(1+z^2) ≤ 85/64 := by
      have hp := mul_le_mul (show 1+z ≤ 5/4 by linarith only [hzmax])
        (show 1+z^2 ≤ 17/16 by linarith only [hz2]) hfac
        (by norm_num : (0:ℝ) ≤ 5/4)
      norm_num at hp
      exact hp
    have hp : 0 ≤ (1+z)*(1+z^2)*(2*z^2+z) := by positivity
    dsimp [descendingE6]
    nlinarith only [hp, hu]

theorem descendingP_lower (z ρ : ℝ) (hz : 0 ≤ z) (hzmax : z ≤ 1/4)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 1/4) :
    descendingE0 z + (493/1024)*ρ ≤ descendingP z ρ := by
  obtain ⟨_,h1,h2,h3,h4,h5,h6⟩ := descending_coefficients z hz hzmax
  have hp1 := mul_le_mul_of_nonneg_right h1 hρ
  have hp2 := mul_le_mul_of_nonneg_right
    (show -2 ≤ descendingE2 z by linarith only [h2]) (sq_nonneg ρ)
  have hp3 := mul_nonneg h3 (pow_nonneg hρ 3)
  have hp4 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hρ 4)
  have hp5 := mul_nonneg h5.le (pow_nonneg hρ 5)
  have hp6 := mul_le_mul_of_nonneg_right
    (show -3 ≤ descendingE6 z by linarith only [h6]) (pow_nonneg hρ 6)
  have hρ3 : ρ^3 ≤ 1/64 := by
    have := power_le_bound hρ hρmax 3
    norm_num at this ⊢
    exact this
  have hρ5 : ρ^5 ≤ 1/1024 := by
    have := power_le_bound hρ hρmax 5
    norm_num at this ⊢
    exact this
  have hbrace : 493/1024 ≤ 1-2*ρ-ρ^3-3*ρ^5 := by
    linarith only [hρmax,hρ3,hρ5]
  have hprod := mul_le_mul_of_nonneg_left hbrace hρ
  dsimp [descendingP]
  nlinarith only [hp1,hp2,hp3,hp4,hp5,hp6,hprod]

/-- The closed descending triangle includes both the zero wall angle and the
equal-angle edge. The latter is strictly positive through its constant term. -/
theorem descendingP_pos (z ρ : ℝ) (hz : 0 ≤ z) (hzmax : z ≤ 1/4)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 1/4) (hsum : 0 < z+ρ) :
    0 < descendingP z ρ := by
  have hlower := descendingP_lower z ρ hz hzmax hρ hρmax
  rcases eq_or_lt_of_le hρ with heq | hpos
  · have hρzero : ρ = 0 := heq.symm
    have hzpos : 0 < z := by linarith only [hsum, hρzero]
    have h0 : 0 < descendingE0 z := by dsimp [descendingE0]; positivity
    linarith only [hlower, h0, hρzero]
  · have h0 : 0 ≤ descendingE0 z := by dsimp [descendingE0]; positivity
    linarith only [hlower,h0,hpos]

end N12Compact.C1092ShallowPositiveScalars
