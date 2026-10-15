import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopScalars
import Mathlib.Tactic.LinearCombination

/-! ORDINARY-LEFT-TOP-OBSTRUCTION.md, Theorem 2 section 2.1.
The two decreasing-function estimates are expressed by an exact lower chord
of the unit circle and polynomial differences. This keeps the whole closed
wall-angle interval, including its axial endpoint, without calculus imports.
Source translation only; no compiler acceptance is claimed. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopExitScalars
set_option Elab.async false

def F (C : ℝ) : ℝ := 7/20-C+(13/50)*C^2
def G (C S : ℝ) : ℝ := 13/20-S+(13/50)*C*S

theorem wall_bounds (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (slope : C ≤ (2/3)*S) :
    C ≤ 3/5 ∧ 4/5 ≤ S ∧ C ≤ 1 ∧ S ≤ 1 := by
  have comparison := mul_nonneg
    (show 0 ≤ 2*S-3*C by linarith only [slope])
    (show 0 ≤ 2*S+3*C by linarith only [cn,sp])
  have cosine : C ≤ 3/5 := by
    apply le_of_not_gt
    intro high
    have product := mul_pos
      (show 0 < C-3/5 by linarith only [high])
      (show 0 < C+3/5 by linarith only [cn])
    nlinarith only [unit,comparison,product]
  have sine : 4/5 ≤ S := by
    apply le_of_not_gt
    intro low
    have product := mul_pos
      (show 0 < 4/5-S by linarith only [low])
      (show 0 < 4/5+S by linarith only [sp])
    nlinarith only [unit,comparison,product]
  have sineOne : S ≤ 1 := by
    nlinarith only [unit,sq_nonneg C,sq_nonneg (S-1)]
  exact ⟨cosine,sine,by linarith only [cosine],sineOne⟩

/-- Strict ownership of P0 below the hypothesized upper-u cap forces
the cosine strictly beyond .31. No approximate square root is introduced. -/
theorem cosine_lower (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (gap : (43/500)*S < (13/50)*C) :
    31/100 < C := by
  have first : 0 < 130*C-43*S := by linarith only [gap]
  have second : 0 < 130*C+43*S := by linarith only [cn,sp]
  have product := mul_pos first second
  apply lt_of_not_ge
  intro low
  have square := mul_nonneg
    (show 0 ≤ 31/100-C by linarith only [low])
    (show 0 ≤ 31/100+C by linarith only [cn])
  nlinarith only [unit,product,square]

private def chord (C : ℝ) : ℝ := (161-75*C)/145

/-- The line joining (.31,.95) to (.6,.8) lies below the unit circle
on the entire interval. The left endpoint has a strict rational margin. -/
private theorem chord_below (C S : ℝ) (cn : 0 ≤ C) (sn : 0 ≤ S)
    (unit : C^2+S^2=1) (lo : 31/100 ≤ C) (hi : C ≤ 3/5) :
    chord C ≤ S := by
  have chordPositive : 0 < chord C := by
    dsimp only [chord]
    linarith only [hi]
  have product := mul_nonneg
    (show 0 ≤ 3-5*C by linarith only [hi])
    (show 0 ≤ 5330*C-1632 by linarith only [lo])
  have identity : S^2-(chord C)^2 =
      (3-5*C)*(5330*C-1632)/21025 := by
    dsimp only [chord]
    linear_combination unit
  apply le_of_not_gt
  intro low
  have bad := mul_pos (sub_pos.mpr low)
    (show 0 < chord C+S by linarith only [chordPositive,sn])
  nlinarith only [identity,product,bad]

/-- Equation (10)'s uniform negative combination, with a polynomial
certificate for the manuscript's monotonicity argument. -/
theorem combined_negative (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (lo : 31/100 ≤ C) (hi : C ≤ 3/5) :
    G C S < 0 ∧ F C+(21/65)*G C S < 0 := by
  have circle := chord_below C S cn sp.le unit lo hi
  have weight : 0 ≤ 1-(13/50)*C := by linarith only [hi]
  have lower := mul_le_mul_of_nonneg_left circle weight
  have gBound : G C S ≤ 13/20-(1-(13/50)*C)*chord C := by
    dsimp only [G]
    nlinarith only [lower]
  have increasing := mul_nonneg
    (show 0 ≤ 3/5-C by linarith only [hi])
    (show 0 ≤ 15/29+(13/50)*(161/145)-
        (13/50)*(15/29)*(C+3/5) by linarith only [hi])
  have gNegative : G C S < 0 := by
    dsimp only [chord] at gBound
    nlinarith only [gBound,increasing]
  have decreasing := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ C-31/100 by linarith only [lo])
    (show (157/725)*(C+31/100)-348547/471250+1/2 ≤ 0 by
      linarith only [hi])
  have combined : F C+(21/65)*G C S < 0 := by
    dsimp only [F,chord] at *
    nlinarith only [gBound,decreasing,lo]
  exact ⟨gNegative,combined⟩

theorem upper_exit_residual (l h C S : ℝ) (lp : 0 < l)
    (angle : (21/65)*l ≤ h) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (lo : 31/100 ≤ C) (hi : C ≤ 3/5) :
    l*F C+h*G C S < 0 := by
  have bounds := combined_negative C S cn sp unit lo hi
  have weighted := mul_le_mul_of_nonpos_right angle bounds.1.le
  have strict := mul_neg_of_pos_of_neg lp bounds.2
  nlinarith only [weighted,strict]

/-- The strict Euclidean distance bound used to reject W's own axis
under the upper-u exit: |T-M|^2=.7946<1. -/
theorem marker_projection (C S : ℝ) (unit : C^2+S^2=1) :
    (61/100)*C+(13/20)*S < 1 := by
  have norm : ((61/100)*C+(13/20)*S)^2 < 1 := by
    nlinarith only [unit,sq_nonneg ((13/20)*C-(61/100)*S)]
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg
    (show 0 ≤ (61/100)*C+(13/20)*S-1 by linarith only [high])
    (show 0 ≤ (61/100)*C+(13/20)*S+1 by linarith only [high])
  nlinarith only [norm,product]

end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopExitScalars
