import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! A closed vertex and a strict marker on opposite sides of one actual
foreign segment force a strict crossing before the closed endpoint. -/
namespace N12Compact.Completion.OtherCases.SharpBarGeometry
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem horizontal_crossing (q : OpenSquare) (X Y x0 y0 h lo hi : ℝ)
    (closed : ClosedInside q X Y) (strict : q.Inside x0 y0)
    (below : y0 < h) (above : h < Y)
    (vertexLower : lo ≤ X) (vertexUpper : X ≤ hi)
    (markerLower : lo ≤ x0) (markerUpper : x0 ≤ hi)
    (avoid : ∀ x : ℝ,lo≤x → x≤hi → ¬q.Inside x h) : False := by
  let t := (Y-h)/(Y-y0)
  have denominator : 0 < Y-y0 := by linarith only [below,above]
  have positive : 0 < t := div_pos (sub_pos.mpr above) denominator
  have small : t < 1 := (div_lt_one denominator).mpr (by linarith only [below])
  have relation : t*(Y-y0)=Y-h := div_mul_cancel₀ _ denominator.ne'
  have identity : (1-t)*Y+t*y0=h := by nlinarith only [relation]
  have lower : lo≤(1-t)*X+t*x0 := by
    have first := mul_nonneg (show 0≤1-t by linarith only [small])
      (sub_nonneg.mpr vertexLower)
    have last := mul_nonneg positive.le (sub_nonneg.mpr markerLower)
    nlinarith only [first,last]
  have upper : (1-t)*X+t*x0≤hi := by
    have first := mul_nonneg (show 0≤1-t by linarith only [small])
      (sub_nonneg.mpr vertexUpper)
    have last := mul_nonneg positive.le (sub_nonneg.mpr markerUpper)
    nlinarith only [first,last]
  have point := WallProfile.strict_closed_segment q X Y x0 y0 t closed strict positive small
  rw [identity] at point
  exact avoid _ lower upper point

private theorem closed_swap (q : OpenSquare) (x y : ℝ)
    (closed : ClosedInside q x y) : ClosedInside (pullSwap q) y x := by
  dsimp only [ClosedInside,pullSwap] at closed ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [closed.1,closed.2.1,closed.2.2.1,closed.2.2.2]

theorem vertical_crossing (q : OpenSquare) (X Y x0 y0 h lo hi : ℝ)
    (closed : ClosedInside q X Y) (strict : q.Inside x0 y0)
    (below : x0 < h) (above : h < X)
    (vertexLower : lo ≤ Y) (vertexUpper : Y ≤ hi)
    (markerLower : lo ≤ y0) (markerUpper : y0 ≤ hi)
    (avoid : ∀ y : ℝ,lo≤y → y≤hi → ¬q.Inside h y) : False :=
  horizontal_crossing (pullSwap q) Y X y0 x0 h lo hi
    (closed_swap q X Y closed) ((inside_pullSwap q y0 x0).mpr strict)
    below above vertexLower vertexUpper markerLower markerUpper
    (fun y lower upper point => avoid y lower upper ((inside_pullSwap q y h).mp point))

#print axioms horizontal_crossing
#print axioms vertical_crossing
end N12Compact.Completion.OtherCases.SharpBarGeometry

