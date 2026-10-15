import Compact.Geometry.PositiveWallOwnedWestFaces
import Compact.Geometry.ClosedPointExclusion

/-! The genuine upper-corner triangle closes the positive-wall branch
when the central square owns (1,2). The wall's northeast vertex is a
closed point of its full square and a strict point of the upper corner.
No orientation restriction on the upper corner is needed. Source only. -/
namespace N12Compact.PositiveWallOwnedWestCorner

open S12 S12Pilot FourSquareAnchors C977CornerCubic

private theorem weighted_lower {a b g p q r z : ℝ}
    (ha : 0<a) (hb : 0<b) (hg : 0<g) (sum : a+b+g=1)
    (hp : z<p) (hq : z<q) (hr : z<r) :
    z<a*p+b*q+g*r := by
  have h₀ := mul_pos ha (sub_pos.mpr hp)
  have h₁ := mul_pos hb (sub_pos.mpr hq)
  have h₂ := mul_pos hg (sub_pos.mpr hr)
  have total := congrArg (fun k : ℝ => k*z) sum
  nlinarith only [h₀,h₁,h₂,total]

/-- This small rectangle is strictly within the triangle of three
genuine upper-corner points. -/
theorem triangle (E : OpenSquare) (x y : ℝ)
    (outward : E.Inside (4/5) 3) (corner : E.Inside 1 3)
    (top : E.Inside 1 (1543/500))
    (xl : 49/50<x) (xu : x<1) (yl : 3<y) (yu : y<151/50) :
    E.Inside x y := by
  let a : ℝ := 5*(1-x)
  let g : ℝ := (500/43)*(y-3)
  let b : ℝ := 1-a-g
  have ha : 0<a := by dsimp [a]; linarith only [xu]
  have hg : 0<g := by dsimp [g]; linarith only [yl]
  have hb : 0<b := by dsimp [a,b,g]; linarith only [xl,yu]
  have sum : a+b+g=1 := by dsimp [b]; ring
  have u : E.c*x+E.s*y = a*((4/5)*E.c+3*E.s)+
      b*(E.c+3*E.s)+g*(E.c+(1543/500)*E.s) := by
    dsimp [a,b,g]; ring
  have v : -E.s*x+E.c*y = a*(3*E.c-(4/5)*E.s)+
      b*(3*E.c-E.s)+g*((1543/500)*E.c-E.s) := by
    dsimp [a,b,g]; ring
  have lowU := weighted_lower ha hb hg sum outward.1 corner.1 top.1
  have highU := weighted_lower ha hb hg sum
    (neg_lt_neg outward.2.1) (neg_lt_neg corner.2.1) (neg_lt_neg top.2.1)
  have lowV := weighted_lower ha hb hg sum outward.2.2.1 corner.2.2.1 top.2.2.1
  have highV := weighted_lower ha hb hg sum
    (neg_lt_neg outward.2.2.2) (neg_lt_neg corner.2.2.2) (neg_lt_neg top.2.2.2)
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [u,v,lowU,highU,lowV,highV]

/-- The true corner point (1,3), together with the lower V face,
forces the wall's upper U face. -/
theorem upper_u (W : OpenSquare) (wn : Normal W.c W.s)
    (side : 1<W.side) (high : W.Inside 1 (12/5))
    (lower : 2*W.c-W.s≤W.loV) (missing : ¬W.Inside 1 3) :
    W.loU+W.side≤W.c+3*W.s := by
  have wb := normal_bounds wn
  have wc : 0<W.c := by linarith only [wb.1]
  apply le_of_not_gt
  intro upper
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [high.1,high.2.2.1,lower,side,wb.2.1,wn.1,wc,upper]

/-- The wall's actual northeast vertex is forced inside the upper
corner. Closed contact is enough to contradict disjoint open interiors. -/
theorem impossible (W E : OpenSquare) (wn : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (high : W.Inside 1 (12/5))
    (lower : 2*W.c-W.s≤W.loV)
    (upper : W.loV+W.side≤3*W.c-(457/500)*W.s)
    (positive : 0<W.s) (small : W.s<43/250)
    (outward : E.Inside (4/5) 3) (corner : E.Inside 1 3)
    (top : E.Inside 1 (1543/500))
    (apart : ∀ x y, ¬(E.Inside x y ∧ W.Inside x y)) : False := by
  have wb := normal_bounds wn
  have wc : 0<W.c := by linarith only [wb.1]
  have capU := upper_u W wn side high lower (fun h => apart 1 3 ⟨corner,h⟩)
  let X : ℝ := W.c*(W.loU+W.side)-W.s*(W.loV+W.side)
  let Y : ℝ := W.s*(W.loU+W.side)+W.c*(W.loV+W.side)
  have u : W.c*X+W.s*Y=W.loU+W.side := by
    dsimp [X,Y]
    linear_combination (W.loU+W.side)*wn.2.2
  have v : -W.s*X+W.c*Y=W.loV+W.side := by
    dsimp [X,Y]
    linear_combination (W.loV+W.side)*wn.2.2
  have closed : ClosedInside W X Y := by
    dsimp [ClosedInside]
    rw [u,v]
    exact ⟨by linarith only [side],le_rfl,by linarith only [side],le_rfl⟩
  have wall0 := FourSquareBLBridge.left_wall W wc.le box
  rw [abs_of_nonneg wn.1] at wall0
  dsimp [centerX] at wall0
  have wall : W.s*(W.loV+W.side)≤W.c*W.loU := by
    nlinarith only [wall0]
  have xSide : W.c*W.side≤X := by dsimp [X]; nlinarith only [wall]
  have square := mul_pos (sub_pos.mpr small)
    (show 0<43/250+W.s by linarith only [positive])
  have wide : 49/50<W.c := by
    by_contra no
    have bound := mul_nonneg
      (show 0≤49/50-W.c by linarith only [no])
      (show 0≤49/50+W.c by linarith only [wb.1])
    nlinarith only [square,bound,wn.2.2]
  have strictSide := mul_pos wc (sub_pos.mpr side)
  have xl : 49/50<X := by linarith only [wide,xSide,strictSide]
  have lowWeighted := mul_nonneg wn.1 (sub_nonneg.mpr lower)
  have capWeighted := mul_nonneg wc.le (sub_nonneg.mpr capU)
  have strictTilt := mul_pos positive (show 0<W.side-W.c by linarith only [side,wb.2.1])
  have xu : X<1 := by
    dsimp [X]
    nlinarith only [lowWeighted,capWeighted,strictTilt,wn.2.2]
  have xy : W.c*Y=W.s*X+(W.loV+W.side) := by linarith only [v]
  have xWeighted := mul_nonneg wn.1 (sub_nonneg.mpr xSide)
  have extraSide := mul_pos (sub_pos.mpr side)
    (show 0<1+W.s*W.c by nlinarith only [mul_nonneg wn.1 wc.le])
  have deficit := mul_nonneg (sub_nonneg.mpr wb.2.1)
    (show 0≤1-W.s by linarith only [small])
  have yScaled : 3*W.c<W.c*Y := by
    nlinarith only [xy,xWeighted,lower,extraSide,deficit]
  have yl : 3<Y := (mul_lt_mul_left wc).mp (by simpa [mul_comm] using yScaled)
  have upperWeighted := mul_nonneg wc.le (sub_nonneg.mpr upper)
  have capTilt := mul_nonneg wn.1 (sub_nonneg.mpr capU)
  have yBound : Y≤3+(43/500)*W.c*W.s := by
    dsimp [Y]
    nlinarith only [upperWeighted,capTilt,wn.2.2]
  have tiltBound := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
  have yu : Y<151/50 := by nlinarith only [yBound,tiltBound,small]
  exact ClosedPointExclusion.outside_of_closed E W X Y apart closed
    (triangle E X Y outward corner top xl xu yl yu)

#print axioms impossible
end N12Compact.PositiveWallOwnedWestCorner
