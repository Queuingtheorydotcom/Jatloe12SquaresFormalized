import Compact.Geometry.PositiveCentralNegativeFloor
import Compact.Geometry.FourSquareBLBridge

/-! Actual positive left-wall face reduction in the central escape.
The point (6/5,2) is a genuine negative-bottom consequence; no false
three-square ownership of (1,2) is used. Both foreign seeds are explicit.
All positive canonical wall angles are covered by the two final branches. -/
namespace N12Compact.PositiveWallEscapeFaces

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

/-- The real upper singleton seed can only escape through an upper face. -/
theorem upper_faces (W : OpenSquare) (normal : Normal W.c W.s)
    (point : W.Inside 1 (12/5)) (missing : ¬W.Inside 1 (72/25)) :
    W.loU+W.side≤W.c+(72/25)*W.s ∨
      W.loV+W.side≤(72/25)*W.c-W.s := by
  have b := normal_bounds normal
  by_cases u : W.loU+W.side≤W.c+(72/25)*W.s
  · exact Or.inl u
  · right
    apply le_of_not_gt
    intro v
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [u,v,point.1,point.2.2.1,normal.1,b.1]

/-- Exclusion of the actual lower singleton's far seed must use W's
lower V face. The other face would force the strict shared point (6/5,2).
This is a whole continuous implication, with no angular subdivision. -/
theorem lower_face (A W : OpenSquare) (normal : Normal W.c W.s)
    (side : 1<W.side)
    (aPoint : A.Inside (6/5) 2)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (12/5))
    (missingTop : ¬W.Inside 1 (72/25))
    (missingFar : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) :
    (187/100)*W.c-(19/25)*W.s≤W.loV := by
  have b := normal_bounds normal
  have hc : 0<W.c := by linarith only [b.1]
  by_contra failure
  have farU : (19/25)*W.c+(187/100)*W.s≤W.loU := by
    apply le_of_not_gt
    intro lower
    apply missingFar
    refine ⟨lower,?_,?_,?_⟩
    · linarith only [marker.2.1,hc,normal.1]
    · linarith only [failure]
    · linarith only [point.2.2.2,hc,normal.2.1]
  rcases upper_faces W normal point missingTop with capU | capV
  · have short : (6/25)*W.c+(101/100)*W.s<1 := by
      linarith only [normal.2.1,b.2.2.2.2.2]
    linarith only [capU,farU,side,short]
  · have shortU : (11/25)*W.c+(13/100)*W.s<1 := by
      nlinarith only [normal.2.2,sq_nonneg (W.c-11/25),
        sq_nonneg (W.s-13/100)]
    have shortV : (22/25)*W.c+(1/5)*W.s<1 := by
      nlinarith only [normal.2.2,sq_nonneg (W.c-22/25),
        sq_nonneg (W.s-1/5)]
    apply apart (6/5) 2
    refine ⟨aPoint,?_,?_,?_,?_⟩
    · linarith only [marker.1,hc]
    · linarith only [farU,side,shortU]
    · linarith only [capV,side,shortV]
    · linarith only [point.2.2.2,hc,normal.1]

private theorem upper_u_tilt (W : OpenSquare) (normal : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (low : (187/100)*W.c-(19/25)*W.s≤W.loV)
    (high : W.loU+W.side≤W.c+(72/25)*W.s) : W.s<3/5 := by
  have b := normal_bounds normal
  have hc : 0<W.c := by linarith only [b.1]
  have wall := FourSquareBLBridge.left_wall W hc.le box
  rw [abs_of_nonneg normal.1] at wall
  dsimp [centerX] at wall
  have leftWall : W.s*(W.loV+W.side)≤W.c*W.loU := by
    linarith only [wall]
  have lowerWeight := mul_nonneg normal.1 (sub_nonneg.mpr low)
  have upperWeight := mul_nonneg hc.le (sub_nonneg.mpr high)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<W.c+W.s by linarith only [hc,normal.1])
  have margin : W.c+W.s-1-(101/100)*W.c*W.s+(6/25)*W.s^2<0 := by
    nlinarith only [leftWall,lowerWeight,upperWeight,width,normal.2.2]
  by_contra failure
  have highTilt : 3/5≤W.s := le_of_not_gt failure
  let K := (W.c+4/5)*(24/125+(6/25)*(W.s+3/5))-
    (W.s+3/5)*(1-(101/100)*W.s)
  have first := mul_nonneg
    (show 0≤W.c-7/10 by linarith only [b.1])
    (show 0≤24/125+(6/25)*(W.s+3/5) by linarith only [normal.1])
  have firstCoefficient : (12/25:ℝ)≤24/125+(6/25)*(W.s+3/5) := by
    linarith only [highTilt]
  have second := mul_nonneg
    (show 0≤W.s+3/5 by linarith only [normal.1])
    (show 0≤197/500-(1-(101/100)*W.s) by linarith only [highTilt])
  have upperSum : W.s+3/5≤8/5 := by linarith only [b.2.2.2.1]
  have kp : 0≤K := by
    dsimp [K]
    nlinarith only [first,firstCoefficient,second,upperSum]
  have comparison := mul_nonneg (sub_nonneg.mpr highTilt) kp
  have identity :
      (W.c+4/5)*(W.c+W.s-1-(101/100)*W.c*W.s+(6/25)*W.s^2-1/625) =
      (W.s-3/5)*K := by
    dsimp [K]
    linear_combination (1-(101/100)*W.s)*normal.2.2
  have bad := mul_neg_of_pos_of_neg
    (show 0<W.c+4/5 by linarith only [hc])
    (show W.c+W.s-1-(101/100)*W.c*W.s+(6/25)*W.s^2-1/625<0 by
      linarith only [margin])
  linarith only [identity,comparison,bad]

/-- The two surviving actual top faces have bounded wall tilts. No branch
is omitted: upper-U gives s<3/5; upper-V gives the sharper s<1/24. -/
theorem faces (A W : OpenSquare) (normal : Normal W.c W.s)
    (side : 1<W.side) (box : InsideContainer W)
    (aPoint : A.Inside (6/5) 2)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (12/5))
    (missingTop : ¬W.Inside 1 (72/25))
    (missingFar : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) :
    (187/100)*W.c-(19/25)*W.s≤W.loV ∧
      ((W.loU+W.side≤W.c+(72/25)*W.s ∧ W.s<3/5) ∨
       (W.loV+W.side≤(72/25)*W.c-W.s ∧ W.s<1/24)) := by
  have low := lower_face A W normal side aPoint marker point missingTop missingFar apart
  refine ⟨low,?_⟩
  rcases upper_faces W normal point missingTop with high | high
  · exact Or.inl ⟨high,upper_u_tilt W normal side box low high⟩
  · have b := normal_bounds normal
    right
    refine ⟨high,?_⟩
    linarith only [high,low,side,b.2.1]

end N12Compact.PositiveWallEscapeFaces
