import Compact.Geometry.PositiveWallEscapeFaces
import Compact.Geometry.IncreasingSegmentAvoidance

/-! Completion of the positive-wall upper-V branch. The central square
need not own either (1,2) or (1,1.88): a variable point on the actual wall's
strict vertical segment yields the contradiction. The alternative upper-U
wall branch is deliberately not claimed here. -/
namespace N12Compact.PositiveWallUpperVImpossible

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem cosine_bound {C S : ℝ} (normal : Normal C S)
    (escape : (C+S)*(1-(7/20)*C)<1) : (81/100:ℝ)<C := by
  have b := normal_bounds normal
  have hc : 0<C := by linarith only [b.1]
  by_contra failure
  have small : C≤81/100 := le_of_not_gt failure
  let Q := 1031/400-(7/5)*(C+81/100)+
    (49/200)*(C^2+(81/100)*C+(81/100)^2)
  have qp : 0≤Q := by
    dsimp [Q]
    nlinarith only [small,hc,sq_nonneg C]
  have weighted := mul_nonneg (sub_nonneg.mpr small) qp
  have polynomial : 0<(13/10:ℝ)-(1031/400)*C+(7/5)*C^2-(49/200)*C^3 := by
    have identity :
        (13/10:ℝ)-(1031/400)*C+(7/5)*C^2-(49/200)*C^3 =
        112391/200000000+(81/100-C)*Q := by dsimp [Q]; ring
    linarith only [weighted,identity]
  have product := mul_pos hc polynomial
  have coefficient : 0≤1-(7/20)*C := by linarith only [b.2.1]
  have bs := mul_nonneg coefficient normal.1
  have difference : 0<1-C+(7/20)*C^2-(1-(7/20)*C)*S := by
    nlinarith only [escape]
  have sum : 0<1-C+(7/20)*C^2+(1-(7/20)*C)*S := by
    linarith only [difference,bs]
  have squares := mul_pos difference sum
  have identity :
      ((1-(7/20)*C)*S)^2-(1-C+(7/20)*C^2)^2 =
      C*((13/10:ℝ)-(1031/400)*C+(7/5)*C^2-(49/200)*C^3) := by
    linear_combination (1-(7/20)*C)^2*normal.2.2
  nlinarith only [squares,product,identity]

private theorem height_margin {C S : ℝ} (normal : Normal C S)
    (escape : (C+S)*(1-(7/20)*C)<1) :
    0<C+S-1-C*S+(3/25)*C^2 := by
  have b := normal_bounds normal
  have large := cosine_bound normal escape
  have lowerSquare := mul_nonneg
    (show 0≤C-81/100 by linarith only [large])
    (show 0≤C+81/100 by linarith only [b.1])
  have product := mul_nonneg
    (show 0≤C^2-6561/10000 by nlinarith only [lowerSquare])
    (show 0≤C^2-3439/10000 by nlinarith only [lowerSquare])
  have scaledUnit := congrArg (fun x : ℝ => C^2*x) normal.2.2
  have crossSquare : (C*S)^2≤(119/250:ℝ)^2 := by
    nlinarith only [product,scaledUnit]
  have cross : C*S≤119/250 := by
    nlinarith only [crossSquare,sq_nonneg (C*S-119/250)]
  have sumSquare : (C+S)^2≤244/125 := by
    nlinarith only [normal.2.2,cross]
  have lo : 0≤C+S-1 := by linarith only [b.2.2.2.2.1]
  have comparison : C+S-1<(7/20)*C*(C+S) := by
    nlinarith only [escape]
  have difference := sub_pos.mpr comparison
  have total : 0<(7/20)*C*(C+S)+(C+S-1) := by
    linarith only [comparison,lo]
  have squares := mul_pos difference total
  have weighted := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr sumSquare)
  have cPositive : 0<C^2 := sq_pos_of_pos (by linarith only [b.1])
  nlinarith only [squares,weighted,cPositive,normal.2.2]

/-- This is only the upper V height of the x=1 section. Its lower U entry
can be above 1.88, so the theorem deliberately does not assert that point. -/
theorem central_height (A : OpenSquare) (normal : Normal A.c A.s)
    (side : 1<A.side) (cap : A.loU+A.side≤2*(A.c+A.s))
    (floor : 1<A.s*A.loU+A.c*A.loV)
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s) :
    (47/25)*A.c-A.s<A.loV+A.side := by
  have b := normal_bounds normal
  have hc : 0<A.c := by linarith only [b.1]
  have uWeight := mul_nonneg normal.1 (sub_nonneg.mpr cap)
  have vWeight := mul_nonneg hc.le (sub_nonneg.mpr northwest)
  have width := mul_pos
    (show 0<A.c+A.s by linarith only [hc,normal.1]) (sub_pos.mpr side)
  have escape : (A.c+A.s)*(1-(7/20)*A.c)<1 := by
    nlinarith only [floor,uWeight,vWeight,width,normal.2.2]
  have margin := height_margin normal escape
  have identity :
      A.c*(A.loV+A.side-((47/25)*A.c-A.s)) =
      (A.s*A.loU+A.c*A.loV-1)+
      A.s*(2*(A.c+A.s)-A.side-A.loU)+
      (A.c+A.s)*(A.side-1)+
      (A.c+A.s-1-A.c*A.s+(3/25)*A.c^2) := by
    linear_combination (-2)*normal.2.2
  have scaled : 0<A.c*(A.loV+A.side-((47/25)*A.c-A.s)) := by
    nlinarith only [identity,floor,uWeight,width,margin]
  have gap := pos_of_mul_pos_right scaled hc.le
  linarith only [gap]

/-- Upper-V escape of the top seed makes W own the entire segment used
below. The upper endpoint was already genuinely owned. -/
theorem wall_point (W : OpenSquare) (normal : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (12/5))
    (low : (187/100)*W.c-(19/25)*W.s≤W.loV)
    (high : W.loV+W.side≤(72/25)*W.c-W.s)
    (tilt : W.s<1/24) : W.Inside 1 (47/25) := by
  have b := normal_bounds normal
  have hc : 0<W.c := by linarith only [b.1]
  have wall := FourSquareBLBridge.left_wall W hc.le box
  rw [abs_of_nonneg normal.1] at wall
  dsimp [centerX] at wall
  have leftWall : W.s*(W.loV+W.side)≤W.c*W.loU := by
    linarith only [wall]
  have lowerWeight := mul_nonneg normal.1 (sub_nonneg.mpr low)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<W.c+W.s by linarith only [hc,normal.1])
  have first := mul_nonneg hc.le (sub_nonneg.mpr b.2.1)
  have second := mul_nonneg normal.1
    (show 0≤1-(1/100)*W.c-(19/25)*W.s by
      linarith only [b.2.1,tilt])
  have scaled : 0<W.c*(W.loU+W.side-(W.c+(47/25)*W.s)) := by
    nlinarith only [leftWall,lowerWeight,width,first,second]
  have upper := pos_of_mul_pos_right scaled hc.le
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,b.1,tilt]
  · linarith only [upper]
  · linarith only [high,side,b.2.1]
  · linarith only [point.2.2.2,hc]

/-- A genuine vertical wall segment intersects the central square at a
variable height. The left-support condition handles the order of its two
active faces, so neither endpoint is assumed to lie in A. -/
theorem segment_impossible (A W : OpenSquare) (normal : Normal A.c A.s)
    (side : 1<A.side) (cap : A.loU+A.side≤2*(A.c+A.s))
    (left : A.c*A.loU-A.s*(A.loV+A.side)<1)
    (height : (47/25)*A.c-A.s<A.loV+A.side)
    (marker : A.Inside (33/20) (33/20)) (west : A.Inside (3/2) 2)
    (first : W.Inside 1 (47/25)) (last : W.Inside 1 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) : False := by
  have b := normal_bounds normal
  have hc : 0<A.c := by linarith only [b.1]
  by_cases zero : A.s=0
  · apply apart 1 (47/25)
    refine ⟨?_,first⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [zero,cap,side,b.2.1,marker.2.2.1,west.2.1,height,hc]
  · have hs : 0<A.s := lt_of_le_of_ne normal.1 (Ne.symm zero)
    have du : 0<A.c*(1-1)+A.s*(12/5-47/25) := by linarith only [hs]
    have dv : 0< -A.s*(1-1)+A.c*(12/5-47/25) := by linarith only [hc]
    have startU : A.loU<A.c*1+A.s*(12/5) := by
      linarith only [cap,side,b.2.1,normal.1]
    have endU : A.c*1+A.s*(12/5)<A.loU+A.side := by
      linarith only [west.2.1,hc,normal.2.1]
    have startV : A.loV< -A.s*1+A.c*(47/25) := by
      linarith only [marker.2.2.1,hc,normal.1]
    have alternatives := IncreasingSegmentAvoidance.dichotomy A W 1 (47/25) 1 (12/5)
      first last du dv startU endU startV apart
    rcases alternatives with above | crossed
    · linarith only [above,height]
    · have determinant :
        (-A.s*(1-1)+A.c*(12/5-47/25))*(A.c*1+A.s*(47/25))-
        (A.c*(1-1)+A.s*(12/5-47/25))*(-A.s*1+A.c*(47/25)) =
        (13/25:ℝ) := by
        linear_combination (13/25)*normal.2.2
      rw [determinant] at crossed
      nlinarith only [crossed,left]

/-- Complete contradiction for the positive-wall upper-V branch, retaining
only actual square premises and the proved negative-bottom horizontal floor. -/
theorem impossible (A W : OpenSquare)
    (an : Normal A.c A.s) (wn : Normal W.c W.s)
    (aSide : 1<A.side) (wSide : 1<W.side) (box : InsideContainer W)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (floor : 1<A.s*A.loU+A.c*A.loV)
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (aMarker : A.Inside (33/20) (33/20)) (aWest : A.Inside (3/2) 2)
    (wMarker : W.Inside (457/500) 2) (wPoint : W.Inside 1 (12/5))
    (low : (187/100)*W.c-(19/25)*W.s≤W.loV)
    (high : W.loV+W.side≤(72/25)*W.c-W.s)
    (tilt : W.s<1/24)
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) : False := by
  exact segment_impossible A W an aSide cap
    (PositiveCentralNegativeFloor.left_support A an aSide cap floor.le)
    (central_height A an aSide cap floor northwest) aMarker aWest
    (wall_point W wn wSide box wMarker wPoint low high tilt) wPoint apart

end N12Compact.PositiveWallUpperVImpossible
