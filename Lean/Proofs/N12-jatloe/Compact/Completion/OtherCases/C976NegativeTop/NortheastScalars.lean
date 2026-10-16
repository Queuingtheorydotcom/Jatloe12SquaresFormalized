import Compact.Completion.CommonCases.CanonicalScalars
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! C976-NEGATIVE-NE-TOP-ENDING.md, section 3.  This is the strict scalar
margin excluding the northeast-square axis.  The three cosine ranges are
the published ones.  Rational projection identities express its endpoint
minimization without square roots or differentiation.  No geometric premise
is added, and neither `S=0` nor the change of sign of `c*C-s*S` is removed.
Source translation only; no compiler replay has been run. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
set_option Elab.async false

private theorem projection_lt_one (c s a b : ℝ) (unit : c^2+s^2=1)
    (margin : a^2+b^2 < 1) : a*c+b*s < 1 := by
  have identity : (a*c+b*s)^2+(b*c-a*s)^2=a^2+b^2 := by
    calc
      _ = (a^2+b^2)*(c^2+s^2) := by ring
      _ = a^2+b^2 := by rw [unit]; ring
  have square : (a*c+b*s)^2 < 1 := by
    linarith only [identity,sq_nonneg (b*c-a*s),margin]
  apply lt_of_not_ge
  intro large
  have product := mul_nonneg
    (show 0 ≤ a*c+b*s-1 by linarith only [large])
    (show 0 ≤ a*c+b*s+1 by linarith only [large])
  nlinarith only [square,product]

/-- Algebraic form of the minimum at `s/c=C/S`.  The quantity
`b*S-p*C` is the signed transverse coefficient at that endpoint.
Its interval `[0,1]` treats both weak signs of the original minimum. -/
private theorem kink_margin (c s C S p b : ℝ)
    (unit : c^2+s^2=1) (unitW : C^2+S^2=1)
    (endpointNonnegative : 0 ≤ p*S+b*C) (endpoint : p*S+b*C < 1)
    (derivativeLow : 0 ≤ b*S-p*C) (derivativeHigh : b*S-p*C ≤ 1) :
    0 < 1-p*c-b*s-min (c*C-s*S) 0 := by
  have identityNorm : (S*c+C*s)^2+(C*c-S*s)^2=1 := by
    calc
      _ = (C^2+S^2)*(c^2+s^2) := by ring
      _ = 1 := by rw [unitW,unit]; norm_num
  have dot : S*c+C*s ≤ 1 := by
    apply le_of_not_gt
    intro large
    have product := mul_pos
      (show 0 < S*c+C*s-1 by linarith only [large])
      (show 0 < S*c+C*s+1 by linarith only [large])
    nlinarith only [identityNorm,sq_nonneg (C*c-S*s),product]
  have comparison := mul_le_mul_of_nonneg_left dot endpointNonnegative
  have identity :
      (p*S+b*C)*(S*c+C*s)-(p*c+b*s) =
        (b*S-p*C)*(C*c-S*s) := by
    linear_combination (p*c+b*s)*unitW
  by_cases sign : 0 ≤ c*C-s*S
  · have product := mul_nonneg derivativeLow sign
    rw [min_eq_right sign]
    nlinarith only [identity,product,comparison,endpoint]
  · have product := mul_nonneg
      (show 0 ≤ 1-(b*S-p*C) by linarith only [derivativeHigh])
      (show 0 ≤ -(c*C-s*S) by linarith only [sign])
    rw [min_eq_left (le_of_not_ge sign)]
    nlinarith only [identity,product,comparison,endpoint]

/-- Positivity at the change-of-sign endpoint.  After multiplication by
`25*(1+S)`, the published endpoint expression is
`43*C^2-36*C+7+(7-11*C)*S`.  Its two rational lower bounds below avoid
the derivative and square-root endpoint calculation. -/
private theorem northeast_endpoint (C S eta : ℝ)
    (cl : 11/20 ≤ C) (sl : 7/10 ≤ S) (su : S ≤ 1)
    (unitW : C^2+S^2=1) (etaPair : eta*(1+S)=C) :
    0 < 2-(36/25)*C+eta*S-(43/25)*S := by
  have polynomial : 0 < 43*C^2-36*C+7+(7-11*C)*S := by
    by_cases split : C ≤ 7/11
    · have first := mul_nonneg
        (show 0 ≤ S-7/10 by linarith only [sl])
        (show 0 ≤ 7-11*C by linarith only [split])
      have second := mul_nonneg
        (show 0 ≤ C-11/20 by linarith only [cl])
        (show 0 ≤ 43*C-401/20 by linarith only [cl])
      nlinarith only [first,second]
    · have first := mul_nonneg
        (show 0 ≤ 1-S by linarith only [su])
        (show 0 ≤ 11*C-7 by linarith only [split])
      have second := mul_nonneg
        (show 0 ≤ C-11/20 by linarith only [cl])
        (show 0 ≤ 43*C-467/20 by linarith only [cl])
      nlinarith only [first,second]
  have identity :
      (1+S)*(2-(36/25)*C+eta*S-(43/25)*S) =
        (43*C^2-36*C+7+(7-11*C)*S)/25 := by
    linear_combination S*etaPair-(43/25)*unitW
  have scaled : 0 < (1+S)*(2-(36/25)*C+eta*S-(43/25)*S) := by
    rw [identity]
    linarith only [polynomial]
  apply lt_of_not_ge
  intro nonpositive
  have product := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 1+S by linarith only [sl]) nonpositive
  exact (not_lt_of_ge product) scaled

/-- The literal `c*f` margin needed by the actual northeast-axis adapter.
All central canonical endpoints, `S=0`, and `c*C-s*S=0` are included. -/
theorem northeast_margin (c s C S : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (Cp : 0 < C) (Sn : 0 ≤ S) (unitW : C^2+S^2=1)
    (ratio : (2/3)*S ≤ C) :
    0 < 1+c*((1-S)/C+S-43/25)-s*(36/25-C)-min (c*C-s*S) 0 := by
  let eta := (1-S)/C
  have Cu : C ≤ 1 := by
    nlinarith only [unitW,sq_nonneg S,sq_nonneg (C-1)]
  have Su : S ≤ 1 := by
    nlinarith only [unitW,sq_nonneg C,sq_nonneg (S-1)]
  have etaNonnegative : 0 ≤ eta :=
    div_nonneg (sub_nonneg.mpr Su) Cp.le
  have etaProduct : eta*C=1-S := div_mul_cancel₀ _ Cp.ne'
  have etaPair : eta*(1+S)=C := by
    dsimp only [eta]
    field_simp [Cp.ne']
    nlinarith only [unitW]
  have etaSum : 1 ≤ eta+S := by
    have identity : C*(eta+S-1)=(1-S)*(1-C) := by
      nlinarith only [etaProduct]
    have product := mul_nonneg (sub_nonneg.mpr Su) (sub_nonneg.mpr Cu)
    apply le_of_not_gt
    intro small
    have negative := mul_neg_of_pos_of_neg Cp
      (show eta+S-1 < 0 by linarith only [small])
    linarith only [identity,product,negative]
  have minBound : min (c*C-s*S) 0 ≤ 0 := min_le_right _ _
  change 0 < 1+c*(eta+S-43/25)-s*(36/25-C)-min (c*C-s*S) 0
  by_cases large : 4/5 ≤ C
  · have projection := projection_lt_one c s (18/25) (16/25) unit (by norm_num)
    have first := mul_le_mul_of_nonneg_left
      (show -(18/25) ≤ eta+S-43/25 by linarith only [etaSum]) cp.le
    have second := mul_le_mul_of_nonneg_right
      (show 36/25-C ≤ 16/25 by linarith only [large]) sn
    nlinarith only [projection,first,second,minBound]
  have notLarge : C ≤ 4/5 := (lt_of_not_ge large).le
  by_cases middle : 7/10 ≤ C
  · have product : (7/50:ℝ) ≤ C*(1-C) := by
      have bound := mul_le_mul middle
        (show (1/5:ℝ) ≤ 1-C by linarith only [notLarge])
        (by norm_num : (0:ℝ) ≤ 1/5) Cp.le
      nlinarith only [bound]
    have identity : (eta+S-1)*(1+S)=C*(1-C) := by
      nlinarith only [etaPair,unitW]
    have scale := mul_nonneg
      (show 0 ≤ eta+S-1 by linarith only [etaSum]) (sub_nonneg.mpr Su)
    have improved : 107/100 ≤ eta+S := by
      nlinarith only [identity,product,scale]
    have projection := projection_lt_one c s (13/20) (37/50) unit (by norm_num)
    have first := mul_le_mul_of_nonneg_left
      (show -(13/20) ≤ eta+S-43/25 by linarith only [improved]) cp.le
    have second := mul_le_mul_of_nonneg_right
      (show 36/25-C ≤ 37/50 by linarith only [middle]) sn
    nlinarith only [projection,first,second,minBound]
  have Csmall : C ≤ 7/10 := (lt_of_not_ge middle).le
  have ratioProduct := mul_nonneg
    (show 0 ≤ C-(2/3)*S by linarith only [ratio])
    (show 0 ≤ C+(2/3)*S by linarith only [Cp,Sn])
  have Clower : 11/20 < C := by
    apply lt_of_not_ge
    intro small
    have square := mul_nonneg
      (show 0 ≤ 11/20-C by linarith only [small])
      (show 0 ≤ 11/20+C by linarith only [Cp])
    nlinarith only [unitW,ratioProduct,square]
  have Slarge : 7/10 < S := by
    have cSquare := mul_nonneg
      (show 0 ≤ 7/10-C by linarith only [Csmall])
      (show 0 ≤ 7/10+C by linarith only [Cp])
    apply lt_of_not_ge
    intro small
    have sSquare := mul_nonneg
      (show 0 ≤ 7/10-S by linarith only [small])
      (show 0 ≤ 7/10+S by linarith only [Sn])
    nlinarith only [unitW,cSquare,sSquare]
  have etaSmall : eta ≤ C := by
    nlinarith only [etaPair,mul_nonneg etaNonnegative Sn]
  let p := 43/25-eta-S
  let b := 36/25-C
  have pp : 0 < p := by
    dsimp only [p]
    linarith only [etaSmall,Csmall,Su]
  have bp : 0 < b := by
    dsimp only [b]
    linarith only [Csmall]
  have endpointNonnegative : 0 ≤ p*S+b*C :=
    add_nonneg (mul_nonneg pp.le Sn) (mul_nonneg bp.le Cp.le)
  have boundary := northeast_endpoint C S eta Clower.le Slarge.le Su unitW etaPair
  have endpoint : p*S+b*C < 1 := by
    dsimp only [p,b]
    nlinarith only [boundary,unitW]
  have transverse : b*S-p*C=1+(11/25)*S-(43/25)*C := by
    dsimp only [p,b]
    nlinarith only [etaProduct]
  have derivativeLow : 0 ≤ b*S-p*C := by
    rw [transverse]
    linarith only [Slarge,Csmall]
  have derivativeHigh : b*S-p*C ≤ 1 := by
    rw [transverse]
    linarith only [Clower,Su]
  have margin := kink_margin c s C S p b unit unitW
    endpointNonnegative endpoint derivativeLow derivativeHigh
  convert margin using 1 <;> dsimp only [p,b] <;> ring

end N12Compact.Completion.OtherCases.C976NegativeTop
