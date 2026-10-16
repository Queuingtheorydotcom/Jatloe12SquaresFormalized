import Compact.Geometry.PositiveWallUpperUPositiveLeft
import Compact.Geometry.PositiveCentralPositiveBottom

/-! Original-point entrance for the complete negative-bottom / positive-left
/ positive-wall sector when the central square misses (1,2). Every face cut
used below is derived here from actual squares, walls and strict ownership.
No unconditional three-square left-point statement is asserted. -/
namespace N12Compact.PositiveWallPositiveLeft

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

structure Cuts (O A : OpenSquare) (t : ℝ) : Prop where
  positive : 0<t
  small : t<1/5
  bottom : t*(O.loU+O.side)≤O.c*O.loV
  cap : O.loU+O.side≤2*O.c-(457/500)*t
  floor : 1<A.s*A.loU+A.c*A.loV
  northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s

/-- The actual missing-left branch supplies the small bottom sector and
the genuine faces needed by the three-square wall cycle. -/
theorem cuts (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aWest : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (missingLeft : ¬A.Inside 1 2) (missingNW : ¬A.Inside (33/20) (47/20))
    (foreignLow : ¬A.Inside 1 (8/5))
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) : Cuts O A t := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  have oSide : 1<O.side := by rwa [same]
  have canonical : |O.s|≤O.c := by
    rw [os,abs_neg,abs_of_nonneg on.1]
    exact on.2.1
  have faces := corner_face O t os on oSide box oMarker oNear oFar missingCorner
  have separator := PositiveCentralTransverse.only_bottom_axis O A oc canonical an
    same side box oMarker oNear oFar missingCorner missingMarker
    aMarker aD aWest aLow cap missingLeft apart
  rw [os,neg_neg] at separator
  have floor0 := PositiveCentralNegativeFloor.of_separation O A t on an side.le cap faces.2.2 separator
  have floorForm : lower A 0 1=A.s*A.loU+A.c*A.loV := by
    rw [lower_in_bands]
    simp only [zero_mul,one_mul,neg_zero,zero_add,add_zero,
      abs_of_nonneg an.1,abs_of_nonneg ac.le]
    ring
  have floor : 1<A.s*A.loU+A.c*A.loV := by rwa [floorForm] at floor0
  have northwest := PositiveCentralLeftBand.northwest_cap A side ac an.1 an.2.1
    aWest aLow missingNW foreignLow
  have centralV := PositiveCentralLeftBand.upper_face A side ac an.1 cap aMarker aWest missingLeft
  have uWeight := mul_nonneg an.1 (sub_nonneg.mpr cap)
  have vWeight := mul_nonneg ac.le (sub_nonneg.mpr northwest)
  have width := mul_pos (show 0<A.c+A.s by linarith only [ac,an.1])
    (sub_pos.mpr side)
  have escape : (A.c+A.s)*(1-(7/20)*A.c)<1 := by
    nlinarith only [floor,uWeight,vWeight,width,an.2.2]
  let K := O.c*A.c-t*A.s
  let D := t*A.c+O.c*A.s
  have kp : 0≤K := by
    have first := mul_nonneg oc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]
    nlinarith only [first,second]
  have dp : 0≤D := add_nonneg (mul_nonneg on.1 ac.le) (mul_nonneg oc.le an.1)
  have form : lower A t O.c=D*A.loU+K*A.loV := by
    rw [lower_in_bands]
    rw [show -t*A.s+O.c*A.c=K by dsimp [K]; ring]
    change D*(A.loU+A.side/2)+K*(A.loV+A.side/2)-
      A.side/2*(|D|+|K|)=D*A.loU+K*A.loV
    rw [abs_of_nonneg dp,abs_of_nonneg kp]
    ring
  have upperU := mul_nonneg dp
    (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
  have upperV := mul_nonneg kp
    (show 0≤2*A.c-A.s-1-A.loV by linarith only [centralV,side])
  have identity : D*(2*(A.c+A.s)-1)+K*(2*A.c-A.s-1) =
      O.c*(2+A.c*A.s-A.c-A.s)+t*(2-A.s^2-A.c+A.s) := by
    dsimp [D,K]
    linear_combination (2*(O.c+t))*an.2.2
  have scalar : boundary O.c t<
      O.c*(2+A.c*A.s-A.c-A.s)+t*(2-A.s^2-A.c+A.s) := by
    nlinarith only [faces.2.2,separator,form,upperU,upperV,identity]
  have small := PositiveCornerSmallBottom.tilt on an escape scalar
  have square := mul_nonneg on.1 (sub_nonneg.mpr small.le)
  have bProduct := mul_nonneg
    (mul_nonneg on.1 (show 0≤1-t by linarith only [small]))
    (sub_nonneg.mpr ob.2.1)
  have bIdentity : O.c*(boundary O.c t-(1+2*t-t^2))=t*(1-t)*(1-O.c) := by
    unfold boundary
    field_simp [oc.ne'] <;> ring
  have boundaryLower : 1+2*t-t^2≤boundary O.c t := by
    have product : 0≤O.c*(boundary O.c t-(1+2*t-t^2)) := by
      linarith only [bIdentity,bProduct]
    have gap := nonneg_of_mul_nonneg_right product oc
    linarith only [gap]
  have markerV : 2*t+(457/500)*O.c<O.loV+O.side := by
    nlinarith only [boundaryLower,faces.2.2,square,small,ob.2.1]
  have marker := (negative_bands O t _ _ os).mp oMarker
  have capO : O.loU+O.side≤2*O.c-(457/500)*t := by
    apply le_of_not_gt
    intro upper
    apply missingMarker
    apply (negative_bands O t 2 (457/500) os).mpr
    refine ⟨?_, (by linarith only [upper]), ?_, (by linarith only [markerV])⟩ <;>
      nlinarith only [marker.1,marker.2.2.1,oc,on.1]
  have positive : 0<t := by
    by_contra failure
    have zero : t=0 := le_antisymm (le_of_not_gt failure) on.1
    nlinarith only [zero,faces.1,capO,oSide,ob.2.1]
  exact ⟨positive,small,faces.2.1,capO,floor,northwest⟩

/-- Complete actual four-square contradiction for this signed sector and
the missing-left branch. The two wall-face alternatives are both handled.
The other signs of L and W remain separate completion obligations. -/
theorem missing_left_impossible (O L A W : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (ln : Normal L.c L.s)
    (an : Normal A.c A.s) (wn : Normal W.c W.s)
    (sameOA : O.side=A.side) (sameLA : L.side=A.side) (sameWA : W.side=A.side)
    (side : 1<A.side) (oBox : InsideContainer O)
    (lBox : InsideContainer L) (wBox : InsideContainer W)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (lMarker : L.Inside (457/500) 1) (lCorner : L.Inside 1 1)
    (lFar : L.Inside (19/25) (187/100)) (lLow : L.Inside 1 (8/5))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aWest : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (missingLeft : ¬A.Inside 1 2) (missingNW : ¬A.Inside (33/20) (47/20))
    (wMarker : W.Inside (457/500) 2) (wPoint : W.Inside 1 (12/5))
    (missingTop : ¬W.Inside 1 (72/25))
    (apartOA : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (apartOL : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (apartLA : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y))
    (apartLW : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y))
    (apartAW : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) : False := by
  have foreignLow : ¬A.Inside 1 (8/5) := fun h => apartLA _ _ ⟨lLow,h⟩
  have foreignFar : ¬W.Inside (19/25) (187/100) := fun h => apartLW _ _ ⟨lFar,h⟩
  have data := cuts O A t os on an sameOA side oBox oMarker oNear oFar
    missingCorner missingMarker aMarker aD aWest aLow cap missingLeft missingNW foreignLow apartOA
  have inner := PositiveCentralNegativeFloor.inner_left_point A an side cap data.floor aMarker aWest
  have wSide : 1<W.side := by rwa [sameWA]
  have lSide : 1<L.side := by rwa [sameLA]
  have wall := PositiveWallEscapeFaces.faces A W wn wSide wBox inner wMarker wPoint
    missingTop foreignFar apartAW
  rcases wall.2 with upperU | upperV
  · exact PositiveWallUpperUPositiveLeft.impossible O L W t os on ln wn
      data.positive data.small.le (sameOA.trans sameLA.symm) (sameLA.trans sameWA.symm)
      lSide lBox wBox data.bottom data.cap upperU.1 oMarker oNear oFar lMarker lCorner lFar
      wMarker apartOL apartLW
  · exact PositiveWallUpperVImpossible.impossible A W an wn side wSide wBox cap
      data.floor data.northwest aMarker aWest wMarker wPoint wall.1 upperV.1 upperV.2 apartAW

end N12Compact.PositiveWallPositiveLeft
