import Compact.Geometry.PositiveCentralPositiveLeft
import Compact.Geometry.PositiveLeftOwnV

/-! The whole positive-left missing-west entrance. Every separating-axis
choice is discharged using the actual O/L/A squares and original points.
No wall-square angle order or unavailable top auxiliary point is assumed. -/
namespace N12Compact.PositiveCentralPositiveLeftWest

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder
set_option Elab.async false

/-- Positive canonical bottom and left frames force the actual central
west point. The proof needs only a strict lower bound on the common side;
there is no additional side upper bound in this signed sector. -/
theorem west (O L A : OpenSquare)
    (on : Normal O.c O.s) (ln : Normal L.c L.s) (an : Normal A.c A.s)
    (sameOA : O.side=A.side) (sameLA : L.side=A.side)
    (side : 1<A.side) (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (oMissingCorner : ¬O.Inside 1 1) (oMissingMarker : ¬O.Inside 2 (457/500))
    (lCorner : L.Inside 1 1) (lNear : L.Inside 1 (28/25))
    (lFar : L.Inside (19/25) (187/100))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aE : A.Inside (87/50) 2) (aLeft : A.Inside (3/2) 2)
    (aLow : A.Inside 2 (3/2)) (cap : A.loU+A.side≤2*(A.c+A.s))
    (aMissingNW : ¬A.Inside (33/20) (47/20)) (aForeignLow : ¬A.Inside 1 (8/5))
    (oaApart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (olApart : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (laApart : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y)) : A.Inside 1 2 := by
  by_contra missing
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have oq : 0≤O.s := on.1
  have aq : 0≤A.s := an.1
  have canonical : |O.s|≤O.c := by rw [abs_of_nonneg on.1]; exact on.2.1
  have oa := PositiveCentralTransverse.only_bottom_axis O A op canonical an sameOA
    side oBox oMarker oNear oFar oMissingCorner oMissingMarker
    aMarker aD aLeft aLow cap missing oaApart
  have westCap := PositiveCentralLeftBand.upper_face A side cp an.1 cap aMarker aLeft missing
  have order := PositiveCentralPositiveBottom.own_axis_angle O A on an sameOA
    side oBox oMarker oNear oMissingCorner oMissingMarker aLeft westCap oa
  have northwest := PositiveCentralLeftBand.northwest_cap A side cp an.1 an.2.1
    aLeft aLow aMissingNW aForeignLow
  have oSide : 1<O.side := by rwa [sameOA]
  have lSide : 1<L.side := by rwa [sameLA]
  have faces := C696PositiveCorner.corner_faces O on oSide oBox
    oMarker oNear oMissingCorner oMissingMarker
  have pB : O.c*B O.c O.s=O.c-2*O.c*O.s+O.s-O.s^2 := by
    unfold B
    field_simp [op.ne'] <;> ring
  have oldBoundary : O.c*C696CornerMargins.boundary O.c O.s=
      O.c+O.s-2*O.c*O.s-(457/500)*O.s^2 := by
    unfold C696CornerMargins.boundary
    field_simp [op.ne'] <;> ring
  have weaker : B O.c O.s≤C696CornerMargins.boundary O.c O.s := by
    have scaled : 0≤O.c*(C696CornerMargins.boundary O.c O.s-B O.c O.s) := by
      nlinarith only [pB,oldBoundary,sq_nonneg O.s]
    have gap := nonneg_of_mul_nonneg_right scaled op
    linarith only [gap]
  have bottom := lt_of_le_of_lt weaker faces.2.2.2.2
  let D := O.c*A.s-O.s*A.c
  let K := O.c*A.c+O.s*A.s
  have cosineOrder := cosine_order an on order.le
  have dp : 0≤D := by
    have first := mul_nonneg on.1 (sub_nonneg.mpr cosineOrder)
    have second := mul_nonneg op.le (sub_nonneg.mpr order.le)
    dsimp [D]
    nlinarith only [first,second]
  have kp : 0≤K := by dsimp [K]; positivity
  have form : lower A (-O.s) O.c=D*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have u : -O.s*A.c+O.c*A.s=D := by dsimp [D]; ring
    have v : -(-O.s)*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg dp,abs_of_nonneg kp]
    ring
  have support : B O.c O.s <
      (O.c*A.s-O.s*A.c)*(2*(A.c+A.s)-1)+
        (O.c*A.c+O.s*A.s)*(A.loV+A.side-1) := by
    have first := mul_nonneg dp
      (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
    have second := mul_nonneg kp (sub_nonneg.mpr side.le)
    rw [form] at oa
    dsimp [D,K] at first second oa
    nlinarith only [bottom,oa,first,second]
  have shallow := PositiveCentralEscapeLeft.bottom_cosine on an order.le support northwest
  have floor := strong_base_bound on an order.le support
  have base := base_bound on an order.le support
  have cosine := (northwest_threshold an base northwest).1
  have wide : 4/5≤A.c := by linarith only [cosine]
  have small : A.s≤3/5 := by
    by_contra no
    have first := mul_pos (sub_pos.mpr cosine)
      (show 0<A.c+81/100 by linarith only [cp])
    have second := mul_pos
      (show 0<A.s-3/5 by linarith only [no])
      (show 0<A.s+3/5 by linarith only [an.1])
    nlinarith only [first,second,an.2.2]
  have la := PositiveCentralPositiveLeft.left_alternatives L A ln an sameLA
    lNear lFar aMarker aE aLow laApart
  rcases CornerSingletonPair.positive_alternatives O L op on.1 lp ln.1
      (sameOA.trans sameLA.symm) oMarker oNear oFar lCorner olApart with own | left
  · rcases la with leftAxis | centralAxis
    · exact PositiveCentralPositiveLeft.own_axis_impossible O L A on ln an
        lSide side lBox order.le shallow.le wide small bottom cap westCap floor own leftAxis
    · exact PositiveCentralPositiveLeft.central_axis_impossible O L A on ln an
        lSide.le side lBox order.le wide small bottom cap own centralAxis
  · rcases la with leftAxis | centralAxis
    · exact (PositiveLeftOwnV.own_axis_impossible O L A on ln an
        oSide lSide side oBox lBox faces.2.2.1 lCorner order.le shallow.le wide small
        cap westCap floor left) leftAxis
    · exact (PositiveLeftOwnV.central_axis_impossible O L A on ln an
        (sameOA.trans sameLA.symm) sameLA side oBox lBox faces.2.2.1 lCorner cap left) centralAxis

#print axioms west
end N12Compact.PositiveCentralPositiveLeftWest
