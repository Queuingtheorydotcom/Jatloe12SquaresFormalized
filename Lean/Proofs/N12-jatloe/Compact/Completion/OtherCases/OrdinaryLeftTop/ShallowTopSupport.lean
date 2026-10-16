import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopExitScalars
import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopDirections
import Compact.Completion.OtherCases.SupportBands
import Compact.Completion.C1092.WholeSupports
import S12.SquareSupportBase

/-! The actual-square support argument in Theorem 2 sections 2.2--2.3 of
ORDINARY-LEFT-TOP-OBSTRUCTION.md. The side, top wall and both lower faces
belong to the same physical W; the two lower ordinary faces belong to N.
The strict side excess remains in each support difference.
Source translation only; no compilation has been requested. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

structure OrdinaryData (N : OpenSquare) : Prop where
  side : 1 < N.side
  cosine : 0 < N.c
  sine : 0 < N.s
  canonical : N.s ≤ N.c
  angleLower : (2/3)*N.c < N.s
  angleUpper : N.s < (8/11)*N.c
  lowerU : -(43/500)*N.c ≤ N.loU
  lowerV : -(27/100)*N.s-(1/25)*N.c ≤ N.loV
  marker : N.Inside (13/20) (7/20)
  high : N.Inside (7/25) 1

structure TopInput (W : OpenSquare) : Prop where
  anchor : W.Inside (11/25) 1
  origin : W.Inside 1 1
  marker : W.Inside 1 (543/500)
  missing : ¬ W.Inside (63/50) 1
  wall : ∀ x y, W.Inside x y → y ≤ 2

theorem TopInput.reframe {W R : OpenSquare} (h : TopInput W)
    (inside : ∀ x y, R.Inside x y ↔ W.Inside x y) : TopInput R where
  anchor := (inside _ _).mpr h.anchor
  origin := (inside _ _).mpr h.origin
  marker := (inside _ _).mpr h.marker
  missing := fun p => h.missing ((inside _ _).mp p)
  wall := fun x y p => h.wall x y ((inside x y).mp p)

structure QuadrantData (W : OpenSquare) : Prop where
  cosine : 0 ≤ W.c
  sine : 0 < W.s
  slope : W.c ≤ (2/3)*W.s

def alpha (N W : OpenSquare) : ℝ := N.c*W.c+N.s*W.s
def gamma (N W : OpenSquare) : ℝ := N.c*W.s-N.s*W.c

theorem coefficients (N W : OpenSquare) (n : OrdinaryData N) (w : QuadrantData W) :
    0 < alpha N W ∧ 0 < gamma N W :=
  ShallowTopDirections.relative_coefficients N.c N.s W.c W.s n.cosine n.sine
    n.canonical w.cosine w.sine w.slope

theorem top_wall_faces (W : OpenSquare) (t : TopInput W) (w : QuadrantData W) :
    W.s*(W.loU+W.side)+W.c*(W.loV+W.side) ≤ 2 := by
  have bound := square_support_bound W 0 1 2
    (by intro x y inside; simpa only [zero_mul,one_mul,zero_add] using t.wall x y inside)
  simp only [squareRadius,zero_mul,one_mul,zero_add,neg_zero,abs_of_nonneg w.cosine,
    abs_of_nonneg w.sine.le] at bound
  dsimp only [centerY] at bound
  linarith only [bound]

theorem lower_ordinary_normal (N W : OpenSquare)
    (n : OrdinaryData N) (w : QuadrantData W) :
    lower W N.c N.s = alpha N W*W.loU-gamma N W*(W.loV+W.side) := by
  have coeff := coefficients N W n w
  have first : N.c*W.c+N.s*W.s=alpha N W := rfl
  have second : -N.c*W.s+N.s*W.c= -gamma N W := by dsimp only [gamma]; ring
  rw [C1092WholeSupports.lower_pn W N.c N.s _ _ first second
    coeff.1.le (by linarith only [coeff.2])]
  ring

theorem upper_wall_normal (N W : OpenSquare)
    (n : OrdinaryData N) (w : QuadrantData W) :
    upper N W.c W.s = alpha N W*(N.loU+N.side)+gamma N W*(N.loV+N.side) := by
  have coeff := coefficients N W n w
  have first : W.c*N.c+W.s*N.s=alpha N W := by dsimp only [alpha]; ring
  have second : -W.c*N.s+W.s*N.c=gamma N W := by dsimp only [gamma]; ring
  rw [C981CompletionSupportForms.upper_in_bands,first,second,
    abs_of_nonneg coeff.1.le,abs_of_nonneg coeff.2.le]
  ring

/-- Equations (11)--(14): the real wall and the one real lower-v face
place W strictly below N's own upper longitudinal face. -/
theorem ordinary_axis_impossible (N W : OpenSquare)
    (n : OrdinaryData N) (t : TopInput W) (w : QuadrantData W)
    (same : N.side=W.side) (face : W.c-(63/50)*W.s ≤ W.loV)
    (separation : upper N N.c N.s ≤ lower W N.c N.s) : False := by
  have coeff := coefficients N W n w
  have wall := top_wall_faces W t w
  have bounds := ShallowTopExitScalars.wall_bounds W.c W.s w.cosine w.sine
    W.unit_normal w.slope
  have side : 1 < W.side := by simpa only [←same] using n.side
  let target := N.c*(W.c-1+W.s*(63/50-W.c))+N.s*W.s*(2-W.s)
  have lowerFormula := lower_ordinary_normal N W n w
  have projection : alpha N W*W.c+gamma N W*W.s=N.c := by
    dsimp only [alpha,gamma]
    linear_combination N.c*W.unit_normal
  have slackWall := mul_nonneg coeff.1.le (sub_nonneg.mpr wall)
  have slackFace := mul_nonneg n.cosine.le (sub_nonneg.mpr face)
  have extra := mul_pos (sub_pos.mpr side)
    (show 0 < alpha N W*W.s+N.c by
      nlinarith only [mul_pos coeff.1 w.sine,n.cosine])
  have identity : target-W.s*lower W N.c N.s =
      alpha N W*(2-W.s*(W.loU+W.side)-W.c*(W.loV+W.side))+
      N.c*(W.loV-(W.c-(63/50)*W.s))+
      (W.side-1)*(alpha N W*W.s+N.c) := by
    rw [lowerFormula]
    dsimp only [target,alpha,gamma]
    linear_combination (W.loV+W.side)*N.c*W.unit_normal
  have strict : W.s*lower W N.c N.s < target := by
    linarith only [identity,slackWall,slackFace,extra]
  have first := mul_nonneg n.cosine.le
    (mul_nonneg (show 0 ≤ 1-W.c by linarith only [bounds.2.2.1])
      (show 0 ≤ 1-W.s by linarith only [bounds.2.2.2]))
  have last := mul_nonneg (mul_nonneg n.sine.le w.sine.le)
    (show 0 ≤ W.s-4/5 by linarith only [bounds.2.1])
  have targetBound : target ≤ W.s*((13/50)*N.c+(6/5)*N.s) := by
    dsimp only [target]
    nlinarith only [first,last]
  have ordinary := ShallowTopScalars.ordinary_projection N.c N.s N.unit_normal
    n.angleUpper.le
  have upperFace : (13/50)*N.c+(6/5)*N.s < upper N N.c N.s := by
    rw [(ownU N).2]
    linarith only [ordinary,n.lowerU,n.side]
  have upperScaled := mul_lt_mul_of_pos_left upperFace w.sine
  have sepScaled := mul_le_mul_of_nonneg_left separation w.sine.le
  linarith only [strict,targetBound,upperScaled,sepScaled]

/-- Equations (15)--(17): the full support difference in W's own axis
is the positive scalar residual plus four nonnegative physical slacks.
The common side supplies the last, strictly positive, summand. -/
theorem wall_axis_impossible (N W : OpenSquare)
    (n : OrdinaryData N) (t : TopInput W) (w : QuadrantData W)
    (same : N.side=W.side) (face : W.c-(63/50)*W.s ≤ W.loV)
    (separation : upper N W.c W.s ≤ lower W W.c W.s) : False := by
  have coeff := coefficients N W n w
  have wall := top_wall_faces W t w
  have side : 1 < W.side := by simpa only [←same] using n.side
  let E := ShallowTopScalars.residual
    (ShallowTopScalars.pCoeff N.c N.s) (ShallowTopScalars.qCoeff N.c N.s) W.c W.s
  have residual : 0 < E := by
    have strict := ShallowTopScalars.coefficient_residual_positive N.c N.s W.c W.s
      n.cosine n.sine.le n.canonical N.unit_normal n.angleLower n.angleUpper
      w.cosine w.sine W.unit_normal w.slope
    have square : 0 < W.s^2 := by nlinarith only [mul_pos w.sine w.sine]
    dsimp only [E]
    linarith only [strict,square]
  have upperFormula := upper_wall_normal N W n w
  have slackU := mul_nonneg (mul_nonneg w.sine.le coeff.1.le)
    (show 0 ≤ N.loU+(43/500)*N.c by linarith only [n.lowerU])
  have slackV := mul_nonneg (mul_nonneg w.sine.le coeff.2.le)
    (show 0 ≤ N.loV+(27/100)*N.s+(1/25)*N.c by linarith only [n.lowerV])
  have slackWall : 0 ≤ 2-W.s*(W.loU+W.side)-W.c*(W.loV+W.side) := by
    linarith only [wall]
  have slackFace := mul_nonneg w.cosine (sub_nonneg.mpr face)
  have extra := mul_pos (sub_pos.mpr side)
    (show 0 < W.s*(alpha N W+gamma N W)+W.s+W.c by
      nlinarith only [mul_pos w.sine (add_pos coeff.1 coeff.2),w.sine,w.cosine])
  have identity : W.s*(upper N W.c W.s-W.loU)-E =
      W.s*alpha N W*(N.loU+(43/500)*N.c)+
      W.s*gamma N W*(N.loV+(27/100)*N.s+(1/25)*N.c)+
      (2-W.s*(W.loU+W.side)-W.c*(W.loV+W.side))+
      W.c*(W.loV-(W.c-(63/50)*W.s))+
      (W.side-1)*(W.s*(alpha N W+gamma N W)+W.s+W.c) := by
    rw [upperFormula,same]
    dsimp only [E,ShallowTopScalars.residual,ShallowTopScalars.pCoeff,
      ShallowTopScalars.qCoeff,alpha,gamma]
    linear_combination W.unit_normal
  have support : W.loU < upper N W.c W.s := by
    apply lt_of_not_ge
    intro low
    have product := mul_nonpos_of_nonneg_of_nonpos w.sine.le
      (show upper N W.c W.s-W.loU ≤ 0 by linarith only [low])
    linarith only [identity,slackU,slackV,slackWall,slackFace,extra,residual,product]
  rw [(ownU W).1] at separation
  linarith only [support,separation]

end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTop
