import Compact.Geometry.ABTransverse

/-! The initial separating-normal reduction in Theorem 2 of
ORDINARY-LEFT-TOP-OBSTRUCTION.md.  Only the actual strict points M, Z and A0
are used.  The two surviving axes remain full physical support inequalities.
Source translation only; no compiler acceptance is claimed. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopDirections
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

theorem forward_cone (N W : OpenSquare) (nx ny : ℝ)
    (unit : nx^2+ny^2=1)
    (marker : N.Inside (13/20) (7/20)) (high : N.Inside (7/25) 1)
    (anchor : W.Inside (11/25) 1)
    (separation : upper N nx ny ≤ lower W nx ny) :
    0 < nx ∧ (21/65)*nx < ny := by
  have z := (strict_bounds N _ _ nx ny unit high).2
  have m := (strict_bounds N _ _ nx ny unit marker).2
  have a := (strict_bounds W _ _ nx ny unit anchor).1
  constructor <;> linarith only [z,m,a,separation]

theorem backward_cone (N W : OpenSquare) (nx ny : ℝ)
    (unit : nx^2+ny^2=1)
    (marker : N.Inside (13/20) (7/20)) (high : N.Inside (7/25) 1)
    (anchor : W.Inside (11/25) 1)
    (separation : upper W nx ny ≤ lower N nx ny) :
    nx < 0 ∧ ny < (21/65)*nx := by
  have z := (strict_bounds N _ _ nx ny unit high).1
  have m := (strict_bounds N _ _ nx ny unit marker).1
  have a := (strict_bounds W _ _ nx ny unit anchor).2
  constructor <;> linarith only [z,m,a,separation]

/-- All four actual square axes and both directions are retained.  The
transverse axes are impossible by the strict point cone; only the two
forward longitudinal supports remain.  `W.c=0` is explicitly permitted. -/
theorem longitudinal_alternatives (N W : OpenSquare)
    (np : 0 < N.c) (ns : 0 ≤ N.s) (wc : 0 ≤ W.c) (ws : 0 < W.s)
    (same : N.side=W.side)
    (marker : N.Inside (13/20) (7/20)) (high : N.Inside (7/25) 1)
    (anchor : W.Inside (11/25) 1)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) :
    upper N N.c N.s ≤ lower W N.c N.s ∨
      upper N W.c W.s ≤ lower W W.c W.s := by
  have axes := CongruentSAT.faceSeparation_of_disjoint N W same apart
  change pairRadius N W ≤ |N.c*(centerX W-centerX N)+N.s*(centerY W-centerY N)| ∨
    pairRadius N W ≤ |-N.s*(centerX W-centerX N)+N.c*(centerY W-centerY N)| ∨
    pairRadius W N ≤ |W.c*(centerX W-centerX N)+W.s*(centerY W-centerY N)| ∨
    pairRadius W N ≤ |-W.s*(centerX W-centerX N)+W.c*(centerY W-centerY N)| at axes
  have sep (nx ny R : ℝ)
      (radius : supportRadius N nx ny+supportRadius W nx ny=R)
      (axis : R ≤ |nx*(centerX W-centerX N)+ny*(centerY W-centerY N)|) :=
    separated N W nx ny (by rwa [radius])
  rcases axes with nu | nv | wu | wv
  · rcases sep _ _ _ (parallel_radius N W) nu with forward | backward
    · exact Or.inl forward
    · have cone := backward_cone N W _ _ N.unit_normal marker high anchor backward
      exact False.elim (by linarith only [cone.1,np])
  · have unit : (-N.s)^2+N.c^2=1 := by nlinarith only [N.unit_normal]
    rcases sep _ _ _ (transverse_radius N W) nv with forward | backward
    · have cone := forward_cone N W _ _ unit marker high anchor forward
      exact False.elim (by linarith only [cone.1,ns])
    · have cone := backward_cone N W _ _ unit marker high anchor backward
      exact False.elim (by linarith only [cone.2,np,ns])
  · have radius : supportRadius N W.c W.s+supportRadius W W.c W.s=pairRadius W N := by
      rw [add_comm]
      exact parallel_radius W N
    rcases sep _ _ _ radius wu with forward | backward
    · exact Or.inr forward
    · have cone := backward_cone N W _ _ W.unit_normal marker high anchor backward
      exact False.elim (by linarith only [cone.1,wc])
  · have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have radius : supportRadius N (-W.s) W.c+supportRadius W (-W.s) W.c=
        pairRadius W N := by
      rw [add_comm]
      exact transverse_radius W N
    rcases sep _ _ _ radius wv with forward | backward
    · have cone := forward_cone N W _ _ unit marker high anchor forward
      exact False.elim (by linarith only [cone.1,ws])
    · have cone := backward_cone N W _ _ unit marker high anchor backward
      exact False.elim (by linarith only [cone.2,wc,ws])

/-- Positivity of the two frame coefficients in equation (9), including
the axial wall frame. The hypotheses are weaker than the published strict
ordinary angle interval. -/
theorem relative_coefficients (l h C S : ℝ) (lp : 0 < l) (hp : 0 < h)
    (order : h ≤ l) (cn : 0 ≤ C) (sp : 0 < S) (slope : C ≤ (2/3)*S) :
    0 < l*C+h*S ∧ 0 < l*S-h*C := by
  constructor
  · nlinarith only [mul_nonneg lp.le cn,mul_pos hp sp]
  · have first := mul_pos lp (show 0 < S-C by linarith only [slope,sp])
    have second := mul_nonneg cn (sub_nonneg.mpr order)
    nlinarith only [first,second]

end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopDirections
