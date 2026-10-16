import Compact.Geometry.FullAuxWallTopEndpoint
import Compact.Geometry.FullAuxWallOppositeAxes
import Compact.Geometry.FullAuxWallSmallTopAngle

/-! A complete signed sector of the full auxiliary-wall configuration.
The opposite central square has a negative canonical frame; B may have
either sign. Actual corner and wall points close the support cycle. No
left-wall angle hypothesis or sampled orientation is used. -/
namespace N12Compact.FullAuxWallNegativeCycle
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

private theorem no_opposite_v (D B : OpenSquare) (S : ℝ)
    (ds : D.s=-S) (dn : Normal D.c S) (bn : Normal B.c B.s)
    (side : 1<B.side) (center : D.Inside 2 2)
    (upperU : B.loU+B.side≤(8/5)*B.c+3*B.s)
    (upperV : B.loV+B.side≤3*B.c-B.s)
    (axis : D.loV+D.side≤lower B S D.c) : False := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let k := S*B.c+D.c*B.s
  let alpha := -S*B.s+D.c*B.c
  have kp : 0≤k := add_nonneg (mul_nonneg dn.1 bc.le) (mul_nonneg dc.le bn.1)
  have ap : 0≤alpha := by
    have p := mul_nonneg (sub_nonneg.mpr dn.2.1) bc.le
    have q := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [alpha]; nlinarith only [p,q]
  have arcProduct := mul_nonneg
    (show 0≤B.c+B.s-1 by linarith only [bb.2.2.2.2.1])
    (show 0≤(3/2 : ℝ)-(B.c+B.s) by linarith only [bb.2.2.2.2.2])
  have arc : 0≤B.c+B.s-1-(3/5)*B.c*B.s := by
    have p := mul_nonneg bc.le bn.1
    nlinarith only [arcProduct,bn.2.2,p]
  have first := mul_nonneg dc.le arc
  have second := mul_nonneg dn.1
    (show 0≤B.c-B.s+(2/5)+(3/5)*B.s^2 by nlinarith only [bn.2.1,sq_nonneg B.s])
  have u := mul_nonneg kp
    (show 0≤(8/5)*B.c+3*B.s-1-B.loU by linarith only [upperU,side])
  have v := mul_nonneg ap
    (show 0≤3*B.c-B.s-1-B.loV by linarith only [upperV,side])
  have identity :
      k*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-2*(D.c+S)=
      -D.c*(B.c+B.s-1-(3/5)*B.c*B.s)-
        S*(B.c-B.s+(2/5)+(3/5)*B.s^2) := by
    dsimp [k,alpha]
    linear_combination (3*D.c+(8/5)*S)*bn.2.2
  rw [lower_pp B S D.c kp ap] at axis
  change D.loV+D.side≤k*B.loU+alpha*B.loV at axis
  have p := center.2.2.2
  rw [ds,neg_neg] at p
  nlinarith only [axis,p,u,v,identity,first,second]

/-- The entire negative-opposite sector closes once its actual A-to-C
support cut has been derived. The three missing B points are physically
owned by the top wall, paired upper corner, and left wall respectively. -/
theorem impossible_of_cut (D B : OpenSquare) (c s S : ℝ)
    (an : Normal c s) (sp : 0<s) (narrowA : 4*s≤c)
    (ds : D.s=-S) (dn : Normal D.c S)
    (bc : 0<B.c) (lowerSign : -B.c≤B.s) (upperSign : B.s≤B.c)
    (side : 1<D.side) (same : D.side=B.side)
    (center : D.Inside 2 2) (southwest : D.Inside (33/20) (33/20))
    (bottom : D.Inside 2 (3/2)) (missingLeft : ¬D.Inside 1 (87/50))
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingTop : ¬B.Inside (8/5) 3) (missingCorner : ¬B.Inside 1 3)
    (missingWall : ¬B.Inside (457/500) 2)
    (apart : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y))
    (cut : (c*D.c-s*S)*(D.loU+D.side-2*(D.c-S))+
      (c*S+s*D.c)*(D.loV+D.side-2*(D.c+S))<(13/50)*s) : False := by
  have reach := FullAuxWallOppositeEscape.narrow_and_left D c s S an sp narrowA
    ds dn side center bottom missingLeft cut
  have modes := transverse D B S ds dn bc lowerSign upperSign same
    center reach.2 southwest marker high apart
  have sideB : 1<B.side := by rwa [←same]
  by_cases positive : 0≤B.s
  · have bn : Normal B.c B.s := ⟨positive,upperSign,B.unit_normal⟩
    have vTop := positive_v D B S ds dn bn sideB center reach.2 low modes
    have upperU : B.loU+B.side≤(8/5)*B.c+3*B.s := by
      apply le_of_not_gt
      intro uTop
      apply missingTop
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [high.1,marker.2.2.1,uTop,vTop,bc,positive]
    have upperV := FullAuxWallOuterCorner.corner_cap B bn sideB upperU marker high missingCorner
    rcases modes with first | second
    · exact no_opposite_v D B S ds dn bn sideB center upperU upperV first
    · let u := D.loU+D.side-2*(D.c-S)
      let v := D.loV+D.side-2*(D.c+S)
      let k := B.s*D.c+B.c*S
      let alpha := B.c*D.c-B.s*S
      have db := normal_bounds dn
      have dc : 0<D.c := by linarith only [db.1]
      have kp : 0≤k := add_nonneg (mul_nonneg positive dc.le) (mul_nonneg bc.le dn.1)
      have ap : 0≤alpha := by
        have p := mul_nonneg (sub_nonneg.mpr dn.2.1) bc.le
        have q := mul_nonneg dn.1 (sub_nonneg.mpr upperSign)
        dsimp [alpha]; nlinarith only [p,q]
      have support : upper D (-B.s) B.c=-k*D.loU+alpha*(D.loV+D.side) := by
        dsimp [upper,supportRadius,centerX,centerY]
        rw [ds]
        rw [abs_of_nonpos (show -B.s*D.c+B.c*(-S)≤0 by dsimp [k] at kp; nlinarith only [kp]),
          abs_of_nonneg (show -(-B.s)*(-S)+B.c*D.c≥0 by dsimp [alpha] at ap; nlinarith only [ap])]
        dsimp [k,alpha]; ring
      have identity : upper D (-B.s) B.c=
          2*(B.c-B.s)+D.side*k-k*u+alpha*v := by
        rw [support]
        dsimp [u,v,k,alpha]
        linear_combination 2*(B.c-B.s)*dn.2.2
      have cap : B.side*(1+k)+alpha*v≤B.c+B.s+k*u := by
        rw [same] at identity
        nlinarith only [identity,second,upperV]
      have up : 0<u := by
        have h := center.2.1
        rw [ds] at h
        dsimp [u]; nlinarith only [h]
      have vp : 0<v := by
        have h := center.2.2.2
        rw [ds,neg_neg] at h
        dsimp [v]; nlinarith only [h]
      have small := FullAuxWallSmallTopAngle.small_top_angle an dn bn sideB sp
        narrowA reach.1.le up vp cut cap
      exact missingWall (FullAuxWallOuterCorner.two_caps_marker B bn small sideB
        upperU upperV marker low)
  · let t := -B.s
    have bs : B.s=-t := by dsimp [t]; ring
    have bn : Normal B.c t :=
      ⟨by dsimp [t]; linarith only [positive],
       by dsimp [t]; linarith only [lowerSign],
       by dsimp [t]; nlinarith only [B.unit_normal]⟩
    exact missingTop (negative_point D B S t ds dn bs bn sideB center marker high modes)

/-- The cut in `impossible_of_cut` is discharged by exhaustive separation
of the actual escaping A and opposite D squares. This is a whole signed
sector theorem, with no assumed SAT selector or numerical enclosure. -/
theorem negative_opposite_impossible (A D B : OpenSquare) (S : ℝ)
    (an : Normal A.c A.s) (sp : 0<A.s) (narrowA : 4*A.s≤A.c)
    (ds : D.s=-S) (dn : Normal D.c S)
    (bc : 0<B.c) (lowerSign : -B.c≤B.s) (upperSign : B.s≤B.c)
    (side : 1<A.side) (sameAD : A.side=D.side) (sameDB : D.side=B.side)
    (aPoint : A.Inside 2 (113/50)) (aMarker : A.Inside (47/20) (47/20))
    (aHigh : A.Inside (5/2) 3) (aTop : A.loV+A.side≤3*A.c-(12/5)*A.s)
    (center : D.Inside 2 2) (southwest : D.Inside (33/20) (33/20))
    (bottom : D.Inside 2 (3/2)) (missingLeft : ¬D.Inside 1 (87/50))
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingTop : ¬B.Inside (8/5) 3) (missingCorner : ¬B.Inside 1 3)
    (missingWall : ¬B.Inside (457/500) 2)
    (ad : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y))
    (db : ∀ x y, ¬(D.Inside x y ∧ B.Inside x y)) : False := by
  have ab := normal_bounds an
  have cb := normal_bounds dn
  have cut := FullAuxWallOppositeAxes.cut A D S side sameAD
    (by linarith only [ab.1]) sp narrowA aPoint aMarker aHigh aTop
    ds (by linarith only [cb.1]) dn.1 dn.2.1 southwest center ad
  exact impossible_of_cut D B A.c A.s S an sp narrowA ds dn bc lowerSign upperSign
    (by rwa [←sameAD]) sameDB center southwest bottom missingLeft marker low high
    missingTop missingCorner missingWall db cut

#print axioms impossible_of_cut
#print axioms negative_opposite_impossible
end N12Compact.FullAuxWallNegativeCycle
