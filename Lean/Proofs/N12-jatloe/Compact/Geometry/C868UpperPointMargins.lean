import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Continuous margins for the actual upper point in the C868 central pair.
The first two comparisons are linear in the second normal and use the two
endpoints of its allowed cone. The last comparison uses coarse exact bounds
on the two stated angular sectors. No angle enumeration is involved. -/
namespace N12Compact.C868UpperPointMargins

open C977CornerCubic
set_option Elab.async false

private theorem axis_cone {c s C S p q : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0 ≤ s*C-c*S)
    (axis : 0 ≤ p) (normal : 0 ≤ c*p+s*q) :
    0 ≤ C*p+S*q := by
  have cb := normal_bounds hn
  have Cb := normal_bounds h
  by_cases zero : s=0
  · have Szero : S=0 := by
      rw [zero] at order
      have product := mul_nonneg
        (show 0≤c-7/10 by linarith only [cb.1]) h.1
      nlinarith only [order,h.1,product]
    rw [Szero]
    nlinarith only [mul_nonneg (show 0≤C by linarith only [Cb.1]) axis]
  · have positive : 0<s := lt_of_le_of_ne hn.1 (Ne.symm zero)
    have first := mul_nonneg h.1 normal
    have second := mul_nonneg order axis
    have identity : s*(C*p+S*q) = S*(c*p+s*q)+(s*C-c*S)*p := by ring
    exact nonneg_of_mul_nonneg_right
      (by linarith only [identity,first,second]) positive

private theorem diagonal_cone {c s C S p q : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : s*C-c*S ≤ 0)
    (normal : 0 ≤ c*p+s*q) (diagonal : 0 ≤ p+q) :
    0 ≤ C*p+S*q := by
  have cb := normal_bounds hn
  by_cases equal : c=s
  · have same : C=S := by
      rw [← equal] at order
      have product := mul_nonneg
        (show 0≤c-7/10 by linarith only [cb.1]) (sub_nonneg.mpr h.2.1)
      nlinarith only [order,h.2.1,product]
    rw [same]
    nlinarith only [mul_nonneg h.1 diagonal]
  · have gap : 0<c-s := by
      have strict : s<c := lt_of_le_of_ne hn.2.1 (Ne.symm equal)
      linarith only [strict]
    have first := mul_nonneg (sub_nonneg.mpr h.2.1) normal
    have second := mul_nonneg
      (show 0≤c*S-s*C by linarith only [order]) diagonal
    have identity : (c-s)*(C*p+S*q) =
        (C-S)*(c*p+s*q)+(c*S-s*C)*(p+q) := by ring
    exact nonneg_of_mul_nonneg_right
      (by linarith only [identity,first,second]) gap

private theorem axis_margin {c s : ℝ} (hn : Normal c s) :
    0≤c-1+(9/100)*c*s+(13/20)*s^2 := by
  have b := normal_bounds hn
  have first := mul_nonneg
    (show 0≤1-c by linarith only [b.2.1])
    (show 0≤(13/20)*c-7/20 by linarith only [b.1])
  have second := mul_nonneg (show 0≤c by linarith only [b.1]) hn.1
  have identity : c-1+(9/100)*c*s+(13/20)*s^2 =
      (1-c)*((13/20)*c-7/20)+(9/100)*c*s := by
    linear_combination (13/20)*hn.2.2
  nlinarith only [identity,first,second]

theorem above {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : 0 ≤ s*C-c*S) :
    0 ≤ (c*C+s*S)-C+(s*C-c*S)*((9/100)*c+(13/20)*s) := by
  have b := normal_bounds hn
  let p := c-1+s*((9/100)*c+(13/20)*s)
  let q := s-c*((9/100)*c+(13/20)*s)
  have axis : 0≤p := by dsimp [p]; nlinarith only [axis_margin hn]
  have normal : 0≤c*p+s*q := by
    have identity : c*p+s*q=1-c := by
      dsimp [p,q]
      linear_combination hn.2.2
    rw [identity]
    linarith only [b.2.1]
  have result := axis_cone hn h order axis normal
  dsimp [p,q] at result
  nlinarith only [result]

theorem below {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (order : s*C-c*S ≤ 0) :
    0 ≤ (c*C+s*S)-C-(s*C-c*S)*((61/100)*c-(13/20)*s) := by
  have b := normal_bounds hn
  let p := c-1-s*((61/100)*c-(13/20)*s)
  let q := s+c*((61/100)*c-(13/20)*s)
  have normal : 0≤c*p+s*q := by
    have identity : c*p+s*q=1-c := by
      dsimp [p,q]
      linear_combination hn.2.2
    rw [identity]
    linarith only [b.2.1]
  have diagonal : 0≤p+q := by
    have chord := mul_nonneg
      (show 0≤c+s-1 by linarith only [b.2.2.2.2.1])
      (show 0≤3/2-(c+s) by linarith only [b.2.2.2.2.2])
    have sum : (4/5)*c*s≤c+s-1 := by nlinarith only [chord,hn.2.2]
    have positive := mul_nonneg (show 0≤c by linarith only [b.1]) hn.1
    have identity : p+q =
        c+s-1+(61/100)*(c-s)^2-(1/25)*c*s+(1/25)*s^2 := by
      dsimp [p,q]
      ring
    nlinarith only [identity,sum,positive,sq_nonneg (c-s),sq_nonneg s]
  have result := diagonal_cone hn h order normal diagonal
  dsimp [p,q] at result
  nlinarith only [result]

private theorem steep_coefficients {c s : ℝ} (hn : Normal c s)
    (hsteep : 61*c≤65*s) :
    (1/4:ℝ)≤s-7/20-(13/20)*s^2+(61/100)*c*s ∧
    -(1/5:ℝ)≤(61/100)*s^2+(13/20)*c*s-c ∧
    (61/100)*s^2+(13/20)*c*s-c≤-(7/100:ℝ) := by
  have b := normal_bounds hn
  have sector := mul_nonneg
    (show 0≤65*s-61*c by linarith only [hsteep])
    (show 0≤65*s+61*c by linarith only [hn.1,b.1])
  have cUpper : c≤3/4 := by
    nlinarith only [sector,hn.2.2,sq_nonneg (c-3/4)]
  have sLower : (2/3:ℝ)≤s := by
    by_contra failure
    have product := mul_nonneg hn.1
      (show 0≤2/3-s by linarith only [failure])
    nlinarith only [sector,hn.2.2,product,failure]
  have squareLower : (4/9:ℝ)≤s^2 := by
    have product := mul_nonneg
      (show 0≤s-2/3 by linarith only [sLower])
      (show 0≤s+2/3 by linarith only [hn.1])
    nlinarith only [product]
  have squareUpper : s^2≤1/2 := by
    have product := mul_nonneg (sub_nonneg.mpr hn.2.1)
      (show 0≤c+s by linarith only [hn.1,b.1])
    nlinarith only [product,hn.2.2]
  have csLower : (7/15:ℝ)≤c*s := by
    have product := mul_nonneg
      (show 0≤c-7/10 by linarith only [b.1]) hn.1
    nlinarith only [product,sLower]
  have csUpper : c*s≤1/2 := by
    nlinarith only [hn.2.2,sq_nonneg (c-s)]
  have first : (1/4:ℝ)≤s-7/20-(13/20)*s^2+(61/100)*c*s := by
    nlinarith only [sLower,squareUpper,csLower]
  have second : -(1/5:ℝ)≤(61/100)*s^2+(13/20)*c*s-c := by
    nlinarith only [squareLower,csLower,cUpper]
  have secondUpper : (61/100)*s^2+(13/20)*c*s-c≤-(7/100:ℝ) := by
    nlinarith only [squareUpper,csUpper,b.1]
  exact ⟨first,second,secondUpper⟩

theorem steep {c s C S : ℝ} (hn : Normal c s) (h : Normal C S)
    (hsteep : 61*c≤65*s) (ashallow : 61*S≤35*C) :
    0 ≤ C*(s-7/20-(13/20)*s^2+(61/100)*c*s)+
      S*((61/100)*s^2+(13/20)*c*s-c) := by
  have B := normal_bounds h
  have bounds := steep_coefficients hn hsteep
  have firstScaled := mul_nonneg
    (show 0≤C by linarith only [B.1]) (sub_nonneg.mpr bounds.1)
  have secondScaled := mul_nonneg h.1 (sub_nonneg.mpr bounds.2.1)
  nlinarith only [firstScaled,secondScaled,ashallow,B.1]

/-- The opposite central sign needs no relative-angle split in this mode. -/
theorem negative_above {c s C T : ℝ} (hn : Normal c s) (h : Normal C T) :
    0≤(c*C-s*T)-C+(13/50)*T+
      (s*C+c*T)*((9/100)*c+(13/20)*s) := by
  have b := normal_bounds hn
  have first := mul_nonneg (sub_nonneg.mpr h.2.1) (axis_margin hn)
  have coefficient : 0≤1-(13/20)*c+(9/100)*s := by
    linarith only [b.2.1,hn.1]
  have second := mul_nonneg h.1
    (mul_nonneg (sub_nonneg.mpr hn.2.1) coefficient)
  have identity :
      (c*C-s*T)-C+(13/50)*T+(s*C+c*T)*((9/100)*c+(13/20)*s) =
      (C-T)*(c-1+(9/100)*c*s+(13/20)*s^2)+
        T*(c-s)*(1-(13/20)*c+(9/100)*s) := by
    linear_combination (37/50)*T*hn.2.2
  nlinarith only [identity,first,second]

theorem negative_steep {c s C T : ℝ} (hn : Normal c s) (h : Normal C T)
    (hsteep : 61*c≤65*s) :
    0≤C*(s-7/20-(13/20)*s^2+(61/100)*c*s)+
      T*((13/50)-((61/100)*s^2+(13/20)*c*s-c)) := by
  have B := normal_bounds h
  have bounds := steep_coefficients hn hsteep
  have first := mul_nonneg (show 0≤C by linarith only [B.1])
    (show 0≤s-7/20-(13/20)*s^2+(61/100)*c*s by linarith only [bounds.1])
  have second := mul_nonneg h.1
    (show 0≤(13/50)-((61/100)*s^2+(13/20)*c*s-c) by
      linarith only [bounds.2.2])
  linarith only [first,second]

end N12Compact.C868UpperPointMargins
