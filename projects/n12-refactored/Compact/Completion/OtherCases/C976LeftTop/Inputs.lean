import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopSupport
import Compact.Completion.OtherCases.LowerCornerSupport

/-! Literal local inputs of C976-LEFT-TOP-ANGLE Theorem 1. The top wall
and every incidence belong to the same actual squares. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

structure LeftInput (N : OpenSquare) : Prop where
  side : 1<N.side
  cosine : 0<N.c
  sine : 0<N.s
  canonical : N.s≤N.c
  angleLower : (21/65)*N.c<N.s
  upperV : N.loV+N.side≤N.c
  lowerV : -(27/100)*N.s-(1/25)*N.c≤N.loV
  marker : N.Inside (13/20) (7/20)
  left : N.Inside (-43/500) 0
  inward : N.Inside 0 (13/50)
  high : N.Inside (1/4) 1
  segment : ∀ t : ℝ,0≤t → t≤1 →
    ¬N.Inside (-6/25+(6/25)*t) (-13/100-(13/100)*t)

abbrev TopInput := OrdinaryLeftTop.ShallowTop.TopInput
abbrev QuadrantData := OrdinaryLeftTop.ShallowTop.QuadrantData
abbrev alpha := OrdinaryLeftTop.ShallowTop.alpha
abbrev beta := OrdinaryLeftTop.ShallowTop.gamma

theorem coefficients (N W : OpenSquare) (n : LeftInput N) (w : QuadrantData W) :
    0<alpha N W ∧ 0<beta N W :=
  OrdinaryLeftTop.ShallowTopDirections.relative_coefficients N.c N.s W.c W.s
    n.cosine n.sine n.canonical w.cosine w.sine w.slope

theorem upper_wall_normal (N W : OpenSquare) (n : LeftInput N) (w : QuadrantData W) :
    upper N W.c W.s=alpha N W*(N.loU+N.side)+beta N W*(N.loV+N.side) := by
  have coeff := coefficients N W n w
  have first : W.c*N.c+W.s*N.s=alpha N W := by dsimp only [alpha,OrdinaryLeftTop.ShallowTop.alpha]; ring
  have last : -W.c*N.s+W.s*N.c=beta N W := by dsimp only [beta,OrdinaryLeftTop.ShallowTop.gamma]; ring
  rw [C981CompletionSupportForms.upper_in_bands,first,last,
    abs_of_nonneg coeff.1.le,abs_of_nonneg coeff.2.le]
  ring

theorem lower_left_normal (N W : OpenSquare) (n : LeftInput N) (w : QuadrantData W) :
    lower W N.c N.s=alpha N W*W.loU-beta N W*(W.loV+W.side) := by
  have coeff := coefficients N W n w
  have first : N.c*W.c+N.s*W.s=alpha N W := rfl
  have last : -N.c*W.s+N.s*W.c= -beta N W := by dsimp only [beta,OrdinaryLeftTop.ShallowTop.gamma]; ring
  rw [C1092WholeSupports.lower_pn W N.c N.s _ _ first last
    coeff.1.le (by linarith only [coeff.2])]
  ring

theorem width (N : OpenSquare) (n : LeftInput N) :
    1<(26/25)*N.c+(27/100)*N.s := by
  linarith only [n.side,n.upperV,n.lowerV]

theorem angle_upper (N : OpenSquare) (n : LeftInput N) : N.s<(8/11)*N.c := by
  apply lt_of_not_ge
  intro bad
  have norm : (11*N.c+8*N.s)^2≤185 := by
    nlinarith only [N.unit_normal,sq_nonneg (8*N.c-11*N.s)]
  have comparison : (26/25)*N.c+(27/100)*N.s≤(68/925)*(11*N.c+8*N.s) := by
    linarith only [bad]
  have squared : ((68/925)*(11*N.c+8*N.s))^2<1 := by
    nlinarith only [norm]
  have short : (68/925)*(11*N.c+8*N.s)<1 := by
    nlinarith only [squared,sq_nonneg ((68/925)*(11*N.c+8*N.s)-1)]
  linarith only [width N n,comparison,short]

end N12Compact.Completion.OtherCases.C976LeftTop
