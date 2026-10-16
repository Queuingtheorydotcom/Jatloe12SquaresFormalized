import Compact.Geometry.CentralWallPairSupport

/-! The downstream ordinary-wall obstruction uses the established crossing
in the same actual central square. Its full support comparisons reuse the
two accepted continuous central/wall scalar margins. -/
namespace N12Compact.C1092InwardCrossingConflict
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem impossible (A R : OpenSquare) (side : 1 < A.side) (same : A.side=R.side)
    (cosine : 0 < A.c) (sine : 0 ≤ A.s)
    (escape : 2*A.c+2*A.s ≤ A.loU)
    (lowerV : -(47/20)*A.s+(33/20)*A.c ≤ A.loV)
    (inward : A.Inside (113/50) 2) (outer : A.Inside (47/20) (53/20))
    (z : ℝ) (nonnegative : 0 ≤ z) (small : z < 2/5)
    (angle : (1+A.c)*z=A.s) (unitAngle : A.s*z=1-A.c)
    (crossing : A.Inside 3 (2+z))
    (box : InsideContainer R) (marker : R.Inside (1543/500) 2)
    (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : False := by
  obtain ⟨W,wc,ws,shape,inside,_⟩ := ClosedFrames.positive_frame R
  have sameW : A.side=W.side := same.trans shape.symm
  have wallSide : 1 < W.side := by simpa only [←sameW] using side
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have missing : ¬ W.Inside 3 (2+z) :=
    fun h => disjoint _ _ ⟨crossing,h⟩
  have face := CentralWallEscape.lower_face W wc ws z nonnegative small wm wh missing
  have walls := CentralWallEscape.wall_inequalities W wallSide wc ws wb z wm face
  have halfSmall := CentralWallEscape.half_angle_lt W.c W.s z wc ws W.unit_normal
    nonnegative walls.1 walls.2
  have narrow := CentralWallEscape.slope_of_half_angle A.c A.s z cosine nonnegative
    angle unitAngle halfSmall
  have cosBound := CentralWallPairAxes.cosine_bound A.c A.s cosine sine A.unit_normal narrow.le
  have order := CentralWallPairAxes.wall_angle_order A.c A.s W.c W.s z cosBound
    sine wc ws A.unit_normal W.unit_normal nonnegative angle walls.2
  have axes := CentralWallPairAxes.alternatives A W side sameW cosine sine narrow.le
    wc ws inward lowerV wm wh z nonnegative small crossing disjoint
  rcases axes with central | wall
  · exact CentralWallPairSupport.central_axis_impossible A W side sameW wb
      cosine sine wc ws narrow.le (sub_nonneg.mpr order.le) escape wm wh central
  · exact CentralWallPairSupport.wall_axis_impossible A W side sameW wb
      cosine sine wc ws narrow.le (sub_nonneg.mpr order.le) escape lowerV outer wm wall

#print axioms impossible
end N12Compact.C1092InwardCrossingConflict
