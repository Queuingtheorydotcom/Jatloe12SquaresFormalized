import Compact.Completion.OtherCases.OrdinaryLeftTop.Main
import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopSupport

/-! The complete actual-square join in Theorem 2 of
ORDINARY-LEFT-TOP-OBSTRUCTION.md. First the hypothesized upper-u exit
is rejected on both possible separating axes. The literal missing point
then forces the lower-v face used by both wall support comparisons.
The final wrapper reindexes W's actual faces and reframes the same N.
Source translation only; these declarations have not been compiled. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

/-- The full quadrant-frame version of the manuscript's Theorem 2.
No cap or separating direction is assumed as a premise. -/
theorem quadrant_impossible (N W : OpenSquare)
    (n : OrdinaryData N) (t : TopInput W) (w : QuadrantData W)
    (same : N.side=W.side)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) : False := by
  have coeff := coefficients N W n w
  have side : 1 < W.side := by simpa only [←same] using n.side
  have axes := ShallowTopDirections.longitudinal_alternatives N W
    n.cosine n.sine.le w.cosine w.sine same n.marker n.high t.anchor apart
  have bounds := ShallowTopExitScalars.wall_bounds W.c W.s w.cosine w.sine
    W.unit_normal w.slope
  have origin := t.origin
  have marker := t.marker
  simp only [OpenSquare.Inside,InBands,mul_one] at origin marker
  have noUpperExit : ¬ W.loU+W.side ≤ (63/50)*W.c+W.s := by
    intro cap
    have gap : (43/500)*W.s < (13/50)*W.c := by
      linarith only [cap,marker.2.1]
    have lowerC := ShallowTopExitScalars.cosine_lower W.c W.s
      w.cosine w.sine W.unit_normal gap
    rcases axes with ordinary | boundary
    · have residual := ShallowTopExitScalars.upper_exit_residual N.c N.s W.c W.s
        n.cosine (by linarith only [n.angleLower,n.cosine])
        w.cosine w.sine W.unit_normal lowerC.le bounds.1
      have capWeight := mul_le_mul_of_nonneg_left cap coeff.1.le
      have originWeight := mul_lt_mul_of_pos_left origin.2.2.2 coeff.2
      have extra := mul_pos (sub_pos.mpr side) coeff.1
      have lowerFormula := lower_ordinary_normal N W n w
      have support : lower W N.c N.s <
          alpha N W*((63/50)*W.c+W.s-1)-gamma N W*(W.c-W.s) := by
        rw [lowerFormula]
        nlinarith only [capWeight,originWeight,extra]
      have identity : alpha N W*((63/50)*W.c+W.s-1)-gamma N W*(W.c-W.s) =
          (13/20)*N.c+(7/20)*N.s+
          N.c*ShallowTopExitScalars.F W.c+N.s*ShallowTopExitScalars.G W.c W.s := by
        dsimp only [alpha,gamma,ShallowTopExitScalars.F,ShallowTopExitScalars.G]
        linear_combination (N.c+N.s)*W.unit_normal
      have strictMarker := (strict_bounds N _ _ N.c N.s N.unit_normal n.marker).2
      linarith only [support,identity,residual,strictMarker,ordinary]
    · have projection := ShallowTopExitScalars.marker_projection W.c W.s W.unit_normal
      have strictMarker := (strict_bounds N _ _ W.c W.s W.unit_normal n.marker).2
      rw [(ownU W).1] at boundary
      linarith only [cap,side,projection,strictMarker,boundary]
  have face : W.c-(63/50)*W.s ≤ W.loV := by
    apply le_of_not_gt
    intro low
    apply t.missing
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [origin.1,w.cosine]
    · exact lt_of_not_ge noUpperExit
    · linarith only [low]
    · linarith only [origin.2.2.2,w.sine]
  rcases axes with ordinary | boundary
  · exact ordinary_axis_impossible N W n t w same face ordinary
  · exact wall_axis_impossible N W n t w same face boundary

/-- The literal nonpositive canonical top-frame statement. The ordinary
square may already be in the positive frame produced by Theorem 1.
The axial endpoint is retained through the zero cosine of `turnFrame W`. -/
theorem nonpositive_impossible (N W : OpenSquare)
    (n : OrdinaryData N) (t : TopInput W)
    (cosine : 0 < W.c) (sine : W.s ≤ 0) (slope : -W.s ≤ (2/3)*W.c)
    (same : N.side=W.side)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) : False := by
  let R := turnFrame W
  have inside : ∀ x y, R.Inside x y ↔ W.Inside x y := by
    intro x y
    exact turnFrame_inside W x y
  have quadrant : QuadrantData R := by
    refine ⟨?_,?_,?_⟩ <;> dsimp only [R,turnFrame]
    · linarith only [sine]
    · exact cosine
    · exact slope
  exact quadrant_impossible N R n (t.reframe inside) quadrant
    (by simpa only [R,turnFrame_side] using same)
    (fun x y pair => apart x y ⟨pair.1,(inside x y).mp pair.2⟩)

/-- Applying both completed theorems to the original physical ordinary
square. Its seven omissions remain the seven separate hypotheses in Input;
no foreign ownership or whole-sector assembly is smuggled into this join. -/
theorem impossible_from_ordinary_input (N W : OpenSquare)
    (n : Input N) (t : TopInput W)
    (cosine : 0 < W.c) (sine : W.s ≤ 0) (slope : -W.s ≤ (2/3)*W.c)
    (same : N.side=W.side)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨R,side,inside,profile,high,_⟩ := frame N n
  have ordinary : OrdinaryData R := {
    side := by simpa only [side] using n.side
    cosine := profile.cosine
    sine := profile.sine
    canonical := profile.canonical
    angleLower := profile.angleLower
    angleUpper := profile.angleUpper
    lowerU := profile.lowerU
    lowerV := profile.lowerV
    marker := (inside _ _).mpr n.marker
    high := high }
  exact nonpositive_impossible R W ordinary t cosine sine slope
    (by simpa only [side] using same)
    (fun x y pair => apart x y ⟨(inside x y).mp pair.1,pair.2⟩)

#print axioms quadrant_impossible
#print axioms impossible_from_ordinary_input
end N12Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTop
