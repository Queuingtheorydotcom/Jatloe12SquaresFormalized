import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Continuous scalar estimates for the wall that owns both auxiliary
points on one side. The strict wall defect is forced by the actual square's
side being greater than one; it excludes the two axis endpoints. -/
namespace N12Compact.DoubleAuxWallMargins
set_option Elab.async false

private theorem wall_bounds (C S : ℝ) (hC : 0<C) (hS : 0≤S)
    (unit : C^2+S^2=1) (delta : 0<1+(9/10)*C*S-C-S) :
    C≤1 ∧ S≤1 ∧ 11/9<C+S ∧ C+S≤10/7 ∧ (21/80)*C<S := by
  have cu : C≤1 := by nlinarith only [unit,sq_nonneg S,hC]
  have su : S≤1 := by nlinarith only [unit,sq_nonneg C,hS]
  have cp := mul_nonneg hC.le hS
  have sumlo : 1≤C+S := by nlinarith only [unit,cp,hC,hS]
  have sumhi : C+S≤10/7 := by
    nlinarith only [unit,sq_nonneg (C-S),hC,hS]
  have high : 11/9<C+S := by
    by_contra no
    have p := mul_nonneg (sub_nonneg.mpr sumlo)
      (show 0≤11-9*(C+S) by linarith only [no])
    nlinarith only [p,delta,unit]
  have sumSquare := mul_pos (sub_pos.mpr high)
    (show 0<C+S+11/9 by linarith only [hC,hS])
  have prod : 20/81<C*S := by nlinarith only [sumSquare,unit]
  have slope : (21/80)*C<S := by
    by_contra no
    have p := mul_nonneg (show 0≤21*C-80*S by linarith only [no])
      (show 0≤80*C-21*S by linarith only [no,hC])
    nlinarith only [p,unit,prod]
  exact ⟨cu,su,high,sumhi,slope⟩

private theorem wall_margins (C S : ℝ) (hC : 0<C) (hS : 0≤S)
    (unit : C^2+S^2=1) (delta : 0<1+(9/10)*C*S-C-S) :
    1+(9/10)*C*S-C-S≤(137/850)*C*(4*S-C) ∧
      1+(9/10)*C*S-C-S≤C*((8/17)*S-(37/850)*C) := by
  have b := wall_bounds C S hC hS unit delta
  have sumlo : 1≤C+S := by linarith only [b.2.2.1]
  have chordProduct := mul_nonneg (sub_nonneg.mpr sumlo)
    (sub_nonneg.mpr b.2.2.2.1)
  have chord : (14/17)*C*S≤C+S-1 := by
    nlinarith only [chordProduct,unit]
  have slope := mul_nonneg hC.le
    (show 0≤S-C/4 by linarith only [b.2.2.2.2,hC])
  have second : 1+(9/10)*C*S-C-S≤C*((8/17)*S-(37/850)*C) := by
    nlinarith only [chord,slope,sq_nonneg C]
  refine ⟨?_,second⟩
  by_cases small : S≤(3/10)*C
  · have sumhi : C+S≤13/10 := by linarith only [small,b.1]
    have product := mul_nonneg (sub_nonneg.mpr sumlo) (sub_nonneg.mpr sumhi)
    have improved : (20/23)*C*S≤C+S-1 := by nlinarith only [product,unit]
    have slope := mul_nonneg hC.le
      (show 0≤S-(21/80)*C by linarith only [b.2.2.2.2])
    nlinarith only [improved,slope,sq_nonneg C]
  · have slope := mul_nonneg hC.le
      (show 0≤S-(3/10)*C by linarith only [small])
    nlinarith only [chord,slope,sq_nonneg C]

/-- The complete scalar interface for the actual-square SAT argument.
The central normal is shallow; the wall normal ranges over the entire
positive quadrant, subject only to its strict actual-wall defect. -/
theorem bounds (c s C S : ℝ) (hc : 0<c) (hs : 0≤s)
    (ac : c^2+s^2=1) (shallow : 4*s≤c)
    (hC : 0<C) (hS : 0≤S) (tc : C^2+S^2=1)
    (delta : 0<1+(9/10)*C*S-C-S) :
    0<c*S-s*C ∧
      0≤(C+S-1)*(c*C+s*S)-(9/10)*s*C ∧
      0≤C*(c*S-s*C)*((1/2)*c+(37/50)*s)-
        (1+(9/10)*C*S-C-S) := by
  have b := wall_bounds C S hC hS tc delta
  have slopes : C/4<S := by linarith only [b.2.2.2.2,hC]
  have p0 := mul_pos hc (sub_pos.mpr slopes)
  have p1 := mul_nonneg hC.le
    (show 0≤c/4-s by linarith only [shallow])
  have cross : 0<c*S-s*C := by nlinarith only [p0,p1]
  have dot : 0≤c*C+s*S := add_nonneg (mul_nonneg hc.le hC.le) (mul_nonneg hs hS)
  have p2 := mul_nonneg (show 0≤C+S-11/9 by linarith only [b.2.2.1]) dot
  have p3 := mul_nonneg hC.le (sub_nonneg.mpr shallow)
  have p4 := mul_nonneg hs (sub_nonneg.mpr slopes.le)
  have p5 := mul_nonneg hs hC.le
  have middle : 0≤(C+S-1)*(c*C+s*S)-(9/10)*s*C := by
    nlinarith only [p2,p3,p4,p5]
  have squareProduct := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0≤c+4*s by linarith only [hc,hs])
  have sSquare : s^2≤1/17 := by nlinarith only [squareProduct,ac]
  have product := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0≤4*c-s by linarith only [hc,shallow])
  have cs : c*s≤4/17 := by nlinarith only [product,ac]
  have margins := wall_margins C S hC hS tc delta
  have expression :
      (c*S-s*C)*((1/2)*c+(37/50)*s)=
        S/2+((37/50)*S-C/2)*(c*s)-(S/2+(37/50)*C)*s^2 := by
    linear_combination (S/2)*ac
  have coefficient : 0≤S/2+(37/50)*C := by linarith only [hC,hS]
  have squareTerm := mul_nonneg coefficient (sub_nonneg.mpr sSquare)
  refine ⟨cross,middle,?_⟩
  by_cases low : 37*S≤25*C
  · have productTerm := mul_nonneg
      (show 0≤C/2-(37/50)*S by linarith only [low])
      (sub_nonneg.mpr cs)
    have lower : (137/850)*(4*S-C)≤
        (c*S-s*C)*((1/2)*c+(37/50)*s) := by
      nlinarith only [expression,squareTerm,productTerm]
    have scaled := mul_nonneg hC.le (sub_nonneg.mpr lower)
    nlinarith only [scaled,margins.1]
  · have productTerm := mul_nonneg
      (show 0≤(37/50)*S-C/2 by linarith only [low])
      (mul_nonneg hc.le hs)
    have lower : (8/17)*S-(37/850)*C≤
        (c*S-s*C)*((1/2)*c+(37/50)*s) := by
      nlinarith only [expression,squareTerm,productTerm]
    have scaled := mul_nonneg hC.le (sub_nonneg.mpr lower)
    nlinarith only [scaled,margins.2]

#print axioms bounds
end N12Compact.DoubleAuxWallMargins
