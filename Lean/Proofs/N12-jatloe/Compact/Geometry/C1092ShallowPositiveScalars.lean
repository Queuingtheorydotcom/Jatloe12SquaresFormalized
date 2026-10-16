import Compact.Geometry.C1092ShallowPositiveScalarsPolynomials
import Mathlib.Tactic.FieldSimp

noncomputable section

/-!
Exact half-angle versions of the C1092 shallow-positive wall scalars. The
physical bridge supplies the actual support inequalities and identifies its
unit normals with `cosH` and `sinH`. This file supplies uniform strict signs,
including all closed edges of both left-wall angle triangles. The bottom-wall
result here is the initial interval and its far endpoint; extension across
the remaining angles is a separate analytic or algebraic argument.
-/

namespace N12Compact.C1092ShallowPositiveScalars

def cosH (x : ℝ) : ℝ := (1-x^2)/(1+x^2)
def sinH (x : ℝ) : ℝ := 2*x/(1+x^2)
def relativeCos (x z : ℝ) : ℝ := cosH x*cosH z + sinH x*sinH z
def relativeSin (x z : ℝ) : ℝ := cosH x*sinH z - sinH x*cosH z
def scalarB (a x : ℝ) : ℝ := a*(3/2 + cosH x*(cosH x+sinH x)/2)
def wallWeight (z : ℝ) : ℝ := 1 + sinH z^2 + sinH z*cosH z
def wallDen (x z : ℝ) : ℝ :=
  x*(1+x^2)*(1+z^2)^2*(1+x*z-x+z)*(1+x*z+x-z)

def leftPlus (a x z : ℝ) : ℝ :=
  cosH z/sinH x * (scalarB a x - 2*cosH x -
    (sinH z - relativeSin x z*(a+sinH x/2))/relativeCos x z) -
    sinH z + a*wallWeight z/2

def leftMinus (a x z : ℝ) : ℝ :=
  cosH z/sinH x * (scalarB a x - 2*cosH x -
    (sinH z + relativeSin x z*(a-cosH x-sinH x))/relativeCos x z) -
    sinH z + a*wallWeight z/2

def bottomMinus (a x z : ℝ) : ℝ := a*wallWeight z/2 +
  (a*((cosH x+sinH x)/2-1/sinH x)+cosH x/sinH x-(11/25)*cosH x^2)*cosH z +
  (-a*sinH x-1+(11/25)*cosH x*sinH x)*sinH z

def bottomSlope (x z : ℝ) : ℝ := wallWeight z/2 +
  ((cosH x+sinH x)/2-1/sinH x)*cosH z - sinH x*sinH z

theorem half_den_pos (x : ℝ) : 0 < 1+x^2 := by positivity

theorem half_unit (x : ℝ) : cosH x^2 + sinH x^2 = 1 := by
  dsimp [cosH,sinH]
  field_simp [(half_den_pos x).ne']
  <;> ring

theorem half_sin_pos (x : ℝ) (hx : 0 < x) : 0 < sinH x := by
  exact div_pos (by linarith only [hx]) (half_den_pos x)

theorem half_cos_pos (x : ℝ) (hx : 0 ≤ x) (hxmax : x < 1) : 0 < cosH x := by
  have hp := mul_pos (sub_pos.mpr hxmax) (show 0 < 1+x by linarith only [hx])
  exact div_pos (by nlinarith only [hp]) (half_den_pos x)

theorem relative_cos_factor (x z : ℝ) :
    relativeCos x z =
      (1+x*z-x+z)*(1+x*z+x-z)/((1+x^2)*(1+z^2)) := by
  dsimp [relativeCos,cosH,sinH]
  field_simp [(half_den_pos x).ne', (half_den_pos z).ne']
  <;> ring

theorem relative_sin_factor (x z : ℝ) :
    relativeSin x z = 2*(z-x)*(1+x*z)/((1+x^2)*(1+z^2)) := by
  dsimp [relativeSin,cosH,sinH]
  field_simp [(half_den_pos x).ne', (half_den_pos z).ne']
  <;> ring

theorem wall_factors_pos (x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z < 1) :
    0 < 1+x*z-x+z ∧ 0 < 1+x*z+x-z := by
  have hxz := mul_nonneg hx.le hz
  constructor <;> linarith only [hx,hxmax,hz,hzmax,hxz]

theorem relative_cos_pos (x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z < 1) : 0 < relativeCos x z := by
  rw [relative_cos_factor]
  obtain ⟨h1,h2⟩ := wall_factors_pos x z hx hxmax hz hzmax
  exact div_pos (mul_pos h1 h2) (mul_pos (half_den_pos x) (half_den_pos z))

theorem wall_den_pos (x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z < 1) : 0 < wallDen x z := by
  obtain ⟨h1,h2⟩ := wall_factors_pos x z hx hxmax hz hzmax
  dsimp [wallDen]
  exact mul_pos (mul_pos (mul_pos (mul_pos hx (half_den_pos x))
    (sq_pos_of_pos (half_den_pos z))) h1) h2

/-- The two divisions by the actual relative cosine are replaced here by its
positive factored numerator before clearing rational denominators. -/
theorem left_plus_one (x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z < 1) :
    leftPlus 1 x z = x*(1-z)*ascendingP x (z-x)/wallDen x z := by
  obtain ⟨hf,hg⟩ := wall_factors_pos x z hx hxmax hz hzmax
  have hfg : 1+z*x*4-z^2+z^2*x^2-x^2 ≠ 0 := by
    convert mul_ne_zero hf.ne' hg.ne' using 1 <;> ring
  dsimp [leftPlus]
  rw [relative_cos_factor, relative_sin_factor]
  dsimp [scalarB,wallWeight,cosH,sinH,wallDen,ascendingP,
    ascendingC0,ascendingC1,ascendingC2,ascendingC3,ascendingC4,ascendingC5]
  field_simp [hx.ne', (half_den_pos x).ne', (half_den_pos z).ne', hf.ne', hg.ne', hfg]
  ring_nf
  field_simp [hfg]
  <;> ring

theorem left_minus_one (x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z < 1) :
    leftMinus 1 x z = (1-z)*descendingP z (x-z)/wallDen x z := by
  obtain ⟨hf,hg⟩ := wall_factors_pos x z hx hxmax hz hzmax
  have hfg : 1+z*x*4-z^2+z^2*x^2-x^2 ≠ 0 := by
    convert mul_ne_zero hf.ne' hg.ne' using 1 <;> ring
  dsimp [leftMinus]
  rw [relative_cos_factor, relative_sin_factor]
  dsimp [scalarB,wallWeight,cosH,sinH,wallDen,descendingP,
    descendingE0,descendingE1,descendingE2,descendingE3,descendingE4,descendingE5,descendingE6]
  field_simp [hx.ne', (half_den_pos x).ne', (half_den_pos z).ne', hf.ne', hg.ne', hfg]
  ring_nf
  field_simp [hfg]
  <;> ring

theorem left_plus_affine (a x z : ℝ) :
    leftPlus a x z = leftPlus 1 x z + (a-1)*
      (cosH z/sinH x*(3/2+cosH x*(cosH x+sinH x)/2+
        relativeSin x z/relativeCos x z)+wallWeight z/2) := by
  dsimp [leftPlus,scalarB]
  ring

theorem left_minus_affine (a x z : ℝ) :
    leftMinus a x z = leftMinus 1 x z + (a-1)*
      (cosH z/sinH x*(3/2+cosH x*(cosH x+sinH x)/2-
        relativeSin x z/relativeCos x z)+wallWeight z/2) := by
  dsimp [leftMinus,scalarB]
  ring

theorem wall_weight_pos (z : ℝ) (hz : 0 ≤ z) (hzmax : z < 1) :
    0 < wallWeight z := by
  have hc := half_cos_pos z hz hzmax
  have hs : 0 ≤ sinH z := div_nonneg (by linarith only [hz]) (half_den_pos z).le
  dsimp [wallWeight]
  have hp := mul_nonneg hs hc.le
  nlinarith only [hp,sq_nonneg (sinH z)]

/-- Uniform left-wall strict separation for the ascending angle triangle.
The equal-angle edge is included; no sampled angles or extra side upper
bound is used. The physical application has `1 < a`, so this is stronger. -/
theorem left_plus_pos (a x z : ℝ) (ha : 1 ≤ a) (hx : 0 < x)
    (hxmax : x ≤ 1/4) (hz : x ≤ z) (hzmax : z < 1) :
    0 < leftPlus a x z := by
  have hz0 : 0 ≤ z := hx.le.trans hz
  have hD := wall_den_pos x z hx hxmax hz0 hzmax
  have hpoly := ascendingP_pos x (z-x) hx (sub_nonneg.mpr hz)
    (by linarith only [hzmax,hx])
  have hbase : 0 < leftPlus 1 x z := by
    rw [left_plus_one x z hx hxmax hz0 hzmax]
    exact div_pos (mul_pos (mul_pos hx (sub_pos.mpr hzmax)) hpoly) hD
  have hc := half_cos_pos x hx.le (by linarith only [hxmax])
  have hs := half_sin_pos x hx
  have hd := half_cos_pos z hz0 hzmax
  have hk := relative_cos_pos x z hx hxmax hz0 hzmax
  have hτ : 0 ≤ relativeSin x z := by
    rw [relative_sin_factor]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hz))
      (by positivity)) (mul_pos (half_den_pos x) (half_den_pos z)).le
  have hw := wall_weight_pos z hz0 hzmax
  have hcoef : 0 ≤ cosH z/sinH x*(3/2+cosH x*(cosH x+sinH x)/2+
        relativeSin x z/relativeCos x z)+wallWeight z/2 := by
    positivity
  rw [left_plus_affine]
  exact add_pos_of_pos_of_nonneg hbase (mul_nonneg (sub_nonneg.mpr ha) hcoef)

/-- Uniform left-wall strict separation for the descending angle triangle,
including the horizontal wall and the equal-angle edge. -/
theorem left_minus_pos (a x z : ℝ) (ha : 1 ≤ a) (hx : 0 < x)
    (hxmax : x ≤ 1/4) (hz : 0 ≤ z) (hzx : z ≤ x) :
    0 < leftMinus a x z := by
  have hzmax : z < 1 := by linarith only [hzx,hxmax]
  have hD := wall_den_pos x z hx hxmax hz hzmax
  have hpoly := descendingP_pos z (x-z) hz (hzx.trans hxmax)
    (sub_nonneg.mpr hzx) (by linarith only [hxmax,hz]) (by linarith only [hx])
  have hbase : 0 < leftMinus 1 x z := by
    rw [left_minus_one x z hx hxmax hz hzmax]
    exact div_pos (mul_pos (sub_pos.mpr hzmax) hpoly) hD
  have hc := half_cos_pos x hx.le (by linarith only [hxmax])
  have hs := half_sin_pos x hx
  have hd := half_cos_pos z hz hzmax
  have hk := relative_cos_pos x z hx hxmax hz hzmax
  have hτ : relativeSin x z ≤ 0 := by
    rw [relative_sin_factor]
    apply div_nonpos_of_nonpos_of_nonneg _ (mul_pos (half_den_pos x) (half_den_pos z)).le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hzx)) (by positivity)
  have htau : 0 ≤ -(relativeSin x z/relativeCos x z) := by
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hτ hk.le)
  have hw := wall_weight_pos z hz hzmax
  have hcoef : 0 ≤ cosH z/sinH x*(3/2+cosH x*(cosH x+sinH x)/2-
        relativeSin x z/relativeCos x z)+wallWeight z/2 := by
    rw [sub_eq_add_neg]
    positivity
  rw [left_minus_affine]
  exact add_pos_of_pos_of_nonneg hbase (mul_nonneg (sub_nonneg.mpr ha) hcoef)

theorem bottom_slope_factor (x z : ℝ) (hx : 0 < x) :
    bottomSlope x z = (x*z+x+z-1)*bottomQ x z /
      (2*x*(1+x^2)*(1+z^2)^2) := by
  dsimp [bottomSlope,wallWeight,cosH,sinH,bottomQ]
  field_simp [hx.ne', (half_den_pos x).ne', (half_den_pos z).ne']
  <;> ring

theorem bottom_side_endpoint (x z : ℝ) (hx : 0 < x) :
    bottomMinus (cosH x+(11/25)*sinH x) x z =
      -(x*z+x+z-1)*bottomP x z/(25*(1+x^2)^2*(1+z^2)^2) := by
  dsimp [bottomMinus,wallWeight,cosH,sinH,bottomP,bottomB0,bottomB1,bottomB2,bottomB3]
  field_simp [hx.ne', (half_den_pos x).ne', (half_den_pos z).ne']
  <;> ring

theorem bottom_affine (a b x z : ℝ) :
    bottomMinus a x z = bottomMinus b x z + (a-b)*bottomSlope x z := by
  dsimp [bottomMinus,bottomSlope]
  ring

/-- The bottom envelope is strictly positive through the first quarter-turn
interval. The generous half-angle endpoint `5/12` is rational and exceeds
`tan (π/8)`; obtaining that angle comparison belongs to the adapter. -/
theorem bottom_minus_initial_pos (a x z : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4)
    (hz : 0 ≤ z) (hzmax : z ≤ 5/12)
    (ha : a ≤ cosH x+(11/25)*sinH x) : 0 < bottomMinus a x z := by
  have hzhalf : z ≤ 1/2 := by linarith only [hzmax]
  have hxz := mul_le_mul hxmax hzhalf hz (by norm_num : (0:ℝ) ≤ 1/4)
  have hF : x*z+x+z-1 < 0 := by linarith only [hxz,hxmax,hzhalf]
  have hQ : 0 < bottomQ x z := by
    have := bottomQ_lower x z hx.le hxmax hz hzhalf
    linarith only [this]
  have hP := bottomP_pos x z hx.le hz hzmax
  have hslope : bottomSlope x z < 0 := by
    rw [bottom_slope_factor x z hx]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hF hQ)
      (mul_pos (mul_pos (mul_pos (by norm_num) hx) (half_den_pos x))
        (sq_pos_of_pos (half_den_pos z)))
  have hbase : 0 < bottomMinus (cosH x+(11/25)*sinH x) x z := by
    rw [bottom_side_endpoint x z hx]
    exact div_pos (mul_pos (neg_pos.mpr hF) hP)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (half_den_pos x)))
        (sq_pos_of_pos (half_den_pos z)))
  rw [bottom_affine a (cosH x+(11/25)*sinH x)]
  exact add_pos_of_pos_of_nonneg hbase
    (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ha) hslope.le)

theorem bottom_far_endpoint_identity (x : ℝ) :
    cosH x+sinH x-1-cosH x*sinH x+sinH x^2/2 =
      2*x^3*(2-x)/(1+x^2)^2 := by
  dsimp [cosH,sinH]
  field_simp [(half_den_pos x).ne']
  <;> ring

theorem bottom_far_endpoint_pos (x : ℝ) (hx : 0 < x) (hxmax : x ≤ 1/4) :
    0 < cosH x+sinH x-1-cosH x*sinH x+sinH x^2/2 := by
  rw [bottom_far_endpoint_identity]
  exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hx 3))
    (by linarith only [hxmax])) (sq_pos_of_pos (half_den_pos x))

end N12Compact.C1092ShallowPositiveScalars
