import Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins

/-! The exact scalar layer of ORDINARY-LEFT-TOP-OBSTRUCTION.md, Theorem 2,
sections 2.2 and 2.3.  These are the published coefficient estimates and
support residual, with rational algebra replacing the square-root bounds.
The physical support inequalities are separate obligations.  Source only:
these declarations have not been submitted to the Lean compiler. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopScalars
set_option Elab.async false

def pCoeff (l h : ℝ) : ℝ :=
  63/50-l+h+(43/500)*l^2-(27/100)*h^2-(1/25)*l*h

def qCoeff (l h : ℝ) : ℝ :=
  l+h-1-(89/250)*l*h-(1/25)*l^2

/-- The four strict estimates immediately preceding equations (16)--(17).
The factorization for the first estimate is
`185*(l-h)^2-9*(l^2+h^2)=(8*l-11*h)*(22*l-16*h)`. -/
theorem central_bounds (l h : ℝ) (lp : 0 < l) (hn : 0 ≤ h)
    (order : h ≤ l) (unit : l^2+h^2=1)
    (lower : (2/3)*l < h) (upper : h < (8/11)*l) :
    11/50 < l-h ∧ 4/13 < h^2 ∧ l^2 < 9/13 ∧ 6/13 < l*h := by
  have first := mul_pos
    (show 0 < 8*l-11*h by linarith only [upper])
    (show 0 < 22*l-16*h by linarith only [order,lp])
  have difference : 11/50 < l-h := by
    apply lt_of_not_ge
    intro small
    have square := mul_nonneg
      (show 0 ≤ 11/50-(l-h) by linarith only [small])
      (show 0 ≤ 11/50+(l-h) by linarith only [order])
    nlinarith only [unit,first,square]
  have hp : 0 < h := by linarith only [lower,lp]
  have second := mul_pos
    (show 0 < 3*h-2*l by linarith only [lower])
    (show 0 < 3*h+2*l by linarith only [hp,lp])
  have sineSquare : 4/13 < h^2 := by nlinarith only [unit,second]
  have cosineSquare : l^2 < 9/13 := by linarith only [unit,sineSquare]
  have third := mul_pos
    (show 0 < 3*h-2*l by linarith only [lower])
    (show 0 < 3*l-2*h by linarith only [order,lp])
  have cross : 6/13 < l*h := by nlinarith only [unit,third]
  exact ⟨difference,sineSquare,cosineSquare,cross⟩

/-- The strict rational margins stated in equations (16) and (17). -/
theorem coefficient_bounds (l h : ℝ) (lp : 0 < l) (hn : 0 ≤ h)
    (order : h ≤ l) (unit : l^2+h^2=1)
    (lower : (2/3)*l < h) (upper : h < (8/11)*l) :
    1/500 < 1-pCoeff l h ∧ 288/1625 < qCoeff l h := by
  obtain ⟨difference,sineSquare,cosineSquare,cross⟩ :=
    central_bounds l h lp hn order unit lower upper
  obtain ⟨_,_,_,_,sum⟩ :=
    N12Compact.CommonCases.CanonicalScalars.bounds l h lp hn order unit
  constructor
  · dsimp only [pCoeff]
    linarith only [difference,sineSquare,cosineSquare,cross]
  · dsimp only [qCoeff]
    linarith only [sum,cosineSquare,cross]

/-- Equation (14), using the rational tangent direction `(11,8)`.
The exact squared endpoint is `13.406^2 < 185`. -/
theorem ordinary_projection (l h : ℝ) (unit : l^2+h^2=1)
    (upper : h ≤ (8/11)*l) : (173/500)*l+(6/5)*h < 1 := by
  have norm : (11*l+8*h)^2 ≤ 185 := by
    nlinarith only [unit,sq_nonneg (8*l-11*h)]
  have comparison :
      (173/500)*l+(6/5)*h ≤ (6703/92500)*(11*l+8*h) := by
    linarith only [upper]
  have square : ((6703/92500)*(11*l+8*h))^2 < 1 := by
    calc
      _ = (6703/92500:ℝ)^2*(11*l+8*h)^2 := by ring
      _ ≤ (6703/92500:ℝ)^2*185 :=
        mul_le_mul_of_nonneg_left norm (sq_nonneg (6703/92500:ℝ))
      _ < 1 := by norm_num
  have endpoint : (6703/92500)*(11*l+8*h) < 1 := by
    apply lt_of_not_ge
    intro failure
    have product := mul_nonneg
      (show 0 ≤ (6703/92500)*(11*l+8*h)-1 by linarith only [failure])
      (show 0 ≤ (6703/92500)*(11*l+8*h)+1 by linarith only [failure])
    nlinarith only [square,product]
  exact lt_of_le_of_lt comparison endpoint

def residual (p q C S : ℝ) : ℝ := C+S-1+q*S^2-p*C*S

/-- The final estimate of section 2.3.  In particular `C=0` is allowed;
only the vertical component `S` must be positive. -/
theorem residual_positive (p q C S : ℝ)
    (pBound : p < 1) (qBound : 1/6 < q)
    (cn : 0 ≤ C) (sp : 0 < S) (unit : C^2+S^2=1)
    (slope : C ≤ (2/3)*S) : S^2/30 < residual p q C S := by
  have order : C ≤ S := by linarith only [slope,sp]
  have unit' : S^2+C^2=1 := by linarith only [unit]
  obtain ⟨_,_,_,_,sum⟩ :=
    N12Compact.CommonCases.CanonicalScalars.bounds S C sp cn order unit'
  have product := mul_nonneg cn sp.le
  have pTerm := mul_le_mul_of_nonneg_right pBound.le product
  have squarePositive : 0 < S^2 := by nlinarith only [mul_pos sp sp]
  have qTerm := mul_lt_mul_of_pos_right qBound squarePositive
  have slopeTerm := mul_le_mul_of_nonneg_right slope sp.le
  dsimp only [residual]
  nlinarith only [sum,pTerm,qTerm,slopeTerm]

/-- The entire published scalar obstruction (15)--(17), with its actual
central coefficients. This does not assume that `C` is strictly positive. -/
theorem coefficient_residual_positive (l h C S : ℝ)
    (lp : 0 < l) (hn : 0 ≤ h) (order : h ≤ l) (centralUnit : l^2+h^2=1)
    (lower : (2/3)*l < h) (upper : h < (8/11)*l)
    (cn : 0 ≤ C) (sp : 0 < S) (wallUnit : C^2+S^2=1)
    (slope : C ≤ (2/3)*S) :
    S^2/30 < residual (pCoeff l h) (qCoeff l h) C S := by
  have coefficients := coefficient_bounds l h lp hn order centralUnit lower upper
  exact residual_positive _ _ C S
    (by linarith only [coefficients.1]) (by linarith only [coefficients.2])
    cn sp wallUnit slope

end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopScalars
