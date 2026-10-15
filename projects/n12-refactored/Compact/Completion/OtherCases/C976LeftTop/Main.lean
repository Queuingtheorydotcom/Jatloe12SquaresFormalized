import Compact.Completion.OtherCases.C976LeftTop.SmallAngles
import Compact.Completion.OtherCases.C976LeftTop.LargeSupports

/-! The complete local Theorem 1 of C976-LEFT-TOP-ANGLE.md.
The genuine point cone supplies both possible separating axes, the actual
omitted point supplies the top lower face, and the whole left-angle range
is treated. The final wrapper only reindexes the same top square's faces.
No C976 ownership table or preceding left-point theorem is assumed proved
by this module. Source only; these declarations have not been compiled. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem quadrant_impossible (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) : False := by
  have axes := Directions.longitudinal_alternatives N W n.cosine n.sine.le
    w.cosine w.sine same n.marker n.high t.anchor apart
  have face := top_lowerV N W n t w same axes
  by_cases small : N.s≤N.c/3
  · exact small_impossible N W n t w same small face axes
  · have large : (1/3)*N.c≤N.s := by linarith only [lt_of_not_ge small]
    rcases axes with leftAxis | topAxis
    · exact left_axis_impossible N W n t w same large face leftAxis
    · exact top_axis_impossible N W n t w same large face topAxis

/-- The original nonpositive top-angle statement, including its axial
endpoint. `turnFrame` changes only the coordinate frame of the same square;
its actual wall, strict anchors and missing point remain the same inputs. -/
theorem nonpositive_impossible (N W : OpenSquare)
    (n : LeftInput N) (t : TopInput W)
    (cosine : 0<W.c) (sine : W.s≤0) (slope : -W.s≤(2/3)*W.c)
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

/-- The continuous steep-angle consequence, with no division at zero. -/
theorem steep_negative (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (cosine : 0<W.c) (sine : W.s≤0) (same : N.side=W.side)
    (apart : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y)) :
    (2/3)*W.c< -W.s := by
  apply lt_of_not_ge
  intro shallow
  exact nonpositive_impossible N W n t cosine sine shallow same apart

#print axioms quadrant_impossible
#print axioms nonpositive_impossible
#print axioms steep_negative
end N12Compact.Completion.OtherCases.C976LeftTop
