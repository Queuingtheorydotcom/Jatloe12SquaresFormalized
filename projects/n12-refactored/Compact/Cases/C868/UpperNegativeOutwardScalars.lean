import Compact.Geometry.C977CornerCubic
import Compact.Completion.CommonCases.UnitCircleChord

/-! Small exact support margins for the negative merged-upper / outward
southeast pair. The outward square's angle bound comes from its genuine
whole-bar span, not an independent interval assumption. -/
namespace N12Compact.C868.UpperNegativeOutwardScalars
open C977CornerCubic
set_option Elab.async false

theorem steep_of_projection (c s : ℝ) (h : Normal c s)
    (projection : 1000<525*c+961*s) : 3/5<s ∧ c<4/5 := by
  have b := normal_bounds h
  have cn : 0≤c := by linarith only [b.1]
  have sine : 3/5<s := by
    apply lt_of_not_ge
    intro low
    have bound := CommonCases.UnitCircleChord.increasing
      (c := (4/5:ℝ)) (s := (3/5:ℝ)) (d := c) (t := s)
      (A := (525:ℝ)) (B := (961:ℝ))
      (by norm_num) cn (by norm_num) h.2.2 (by norm_num) h.1 low
      (by norm_num) (by norm_num) (by norm_num)
    linarith only [bound,projection]
  refine ⟨sine,?_⟩
  apply lt_of_not_ge
  intro high
  have first := mul_nonneg (show 0≤c-4/5 by linarith only [high])
    (show 0≤c+4/5 by linarith only [cn])
  have last := mul_pos (show 0<s-3/5 by linarith only [sine])
    (show 0<s+3/5 by linarith only [sine])
  nlinarith only [first,last,h.2.2]

/-- The endpoint is the exact unit-circle point with half-angle 143/500. -/
theorem outward_sine_cap (d t : ℝ) (h : Normal d t)
    (span : 1<d+(143/500)*t) : t<143000/270449 := by
  have b := normal_bounds h
  apply lt_of_not_ge
  intro high
  have bound := CommonCases.UnitCircleChord.decreasing
    (c := (229551/270449:ℝ)) (s := (143000/270449:ℝ)) (d := d) (t := t)
    (A := (1:ℝ)) (B := (143/500:ℝ))
    (by norm_num) (by linarith only [b.1]) (by norm_num) h.2.2
    (by norm_num) h.1 high (by norm_num) (by norm_num) (by norm_num)
  norm_num at bound
  linarith only [bound,span]

private theorem coefficients (c s : ℝ) (h : Normal c s)
    (steep : 3/5≤s) (cosine : c≤4/5) :
    1-c-s+(543/500)*c*s+(13/50)*s^2≤13/50 ∧
      1+c-s-(13/50)*c*s+(543/500)*s^2≤147/100 := by
  let L := c+s
  let D := c-s
  have b := normal_bounds h
  have Dn : 0≤D := by dsimp only [D]; linarith only [h.2.1]
  have Du : D≤1/5 := by dsimp only [D]; linarith only [cosine,steep]
  have Ln : 0≤L := by dsimp only [L]; linarith only [b.1,h.1]
  have circle : L^2+D^2=2 := by dsimp only [L,D]; nlinarith only [h.2.2]
  have Dsq : D^2≤1/25 := by
    have product := mul_nonneg (sub_nonneg.mpr Du) (show 0≤1/5+D by linarith only [Dn])
    nlinarith only [product]
  have Ll : 7/5≤L := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<7/5-L by linarith only [bad])
      (show 0<7/5+L by linarith only [Ln])
    nlinarith only [product,circle,Dsq]
  have Lu : L≤99/70 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<L-99/70 by linarith only [bad])
      (show 0<L+99/70 by linarith only [Ln])
    nlinarith only [product,circle,sq_nonneg D]
  have firstIdentity : 1-c-s+(543/500)*c*s+(13/50)*s^2=
      587/1000-L+(543/1000)*L^2-(13/100)*L*D := by
    dsimp only [L,D]
    linear_combination (-413/1000)*(h.2.2)
  have lastIdentity : 1+c-s-(13/50)*c*s+(543/500)*s^2=
      1413/1000+D-(543/1000)*L*D+(13/100)*D^2 := by
    dsimp only [L,D]
    linear_combination (413/1000)*(h.2.2)
  have LD := mul_nonneg Ln Dn
  have firstMonotone := mul_nonneg (sub_nonneg.mpr Lu)
    (show 0≤(543/1000)*(99/70+L)-1 by linarith only [Ll])
  have lowerL := mul_nonneg Dn (sub_nonneg.mpr Ll)
  constructor
  · nlinarith only [firstIdentity,LD,firstMonotone]
  · nlinarith only [lastIdentity,lowerL,Du,Dsq]

/-- This is the margin against the southeast square's own U separator.
It is deliberately separate from the other square's U separator. -/
theorem right_axis_margin (c s d t : ℝ) (h : Normal c s) (b : Normal d t)
    (projection : 1000<525*c+961*s) (span : 1<d+(143/500)*t) :
    1/500≤1+(c*d+s*t)+(s*d-c*t)-d-t-
      s*((543/500)*(c*d+s*t)+(13/50)*(s*d-c*t)) := by
  have steep := steep_of_projection c s h projection
  have bounds := coefficients c s h steep.1.le steep.2.le
  have eb := normal_bounds b
  have first := mul_nonneg (show 0≤d by linarith only [eb.1])
    (sub_nonneg.mpr bounds.1)
  have last := mul_nonneg b.1 (sub_nonneg.mpr bounds.2)
  have cap := outward_sine_cap d t b span
  have endpoint := CommonCases.UnitCircleChord.increasing
    (c := (229551/270449:ℝ)) (s := (143000/270449:ℝ)) (d := d) (t := t)
    (A := (13/50:ℝ)) (B := (147/100:ℝ))
    (by norm_num) (by linarith only [eb.1]) (by norm_num) b.2.2
    (by norm_num) b.1 cap.le (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [first,last,endpoint]

#print axioms right_axis_margin
end N12Compact.C868.UpperNegativeOutwardScalars
