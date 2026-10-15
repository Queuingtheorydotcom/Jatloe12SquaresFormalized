import Compact.Geometry.PositiveBottomNegativeWallMixed

/-! The steep negative singleton cannot precede a negative bottom wall
which lies below the negative central neighbor on the wall's own axis.
The marker and both genuine neighbor caps suffice; the full square
supports are retained throughout. -/
namespace N12Compact.NegativeBottomOwnTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
set_option Elab.async false

private theorem neighbor_support (B : OpenSquare) (t : ℝ) {d r : ℝ}
    (bs : B.s=-t) (bn : Normal B.c t) (dn : Normal d r)
    (side : 1≤B.side) (small : t≤3/10)
    (marker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t) :
    lower B r d≤(47/20)*r+(13/10)*d := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have bp : 0≤B.c := by linarith only [bb.1]
  have dp : 0≤d := by linarith only [db.1]
  have wide : 9/10≤B.c := by
    have square := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤3/10+t by linarith only [bn.1])
    by_contra failure
    have compare := mul_nonneg (show 0≤9/10-B.c by linarith only [failure])
      (show 0≤9/10+B.c by linarith only [bb.1])
    nlinarith only [square,compare,bn.2.2]
  let K := r*B.c-d*t
  let H := r*t+d*B.c
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg dn.1 bn.1) (mul_nonneg dp bp)
  by_cases kp : 0≤K
  · let X := 3+B.c*t-B.c-t
    let Y := 2-t^2+t-B.c
    have formula : lower B r d=K*B.loU+H*B.loV :=
      lower_negative_pos B t _ _ bs kp hp
    have first := mul_nonneg kp (sub_nonneg.mpr capU)
    have last := mul_nonneg hp (sub_nonneg.mpr capV)
    have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr side)
    have identity : K*(3*B.c-t-1)+H*(2*B.c+3*t-1)=r*X+d*Y := by
      dsimp [K,H,X,Y]
      linear_combination (3*r+2*d)*bn.2.2
    have xBound : X≤47/20 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
      dsimp [X]; nlinarith only [product,wide]
    have yBound : Y≤13/10 := by
      have product := mul_nonneg bp (sub_nonneg.mpr bb.2.1)
      dsimp [Y]; nlinarith only [product,bn.2.2,small]
    have xWeight := mul_nonneg dn.1 (sub_nonneg.mpr xBound)
    have yWeight := mul_nonneg dp (sub_nonneg.mpr yBound)
    nlinarith only [formula,first,last,width,identity,xWeight,yWeight]
  · have kn : K≤0 := le_of_lt (lt_of_not_ge kp)
    let X := 47/20+(13/20)*t^2+(7/20)*B.c*t-t
    let Y := 2-(7/20)*t^2+(13/20)*B.c*t-B.c
    have formula : lower B r d=K*(B.loU+B.side)+H*B.loV :=
      lower_negative_nonpos B t _ _ bs kn hp
    have marked := (negative_bands B t _ _ bs).mp marker
    have first := mul_nonneg (neg_nonneg.mpr kn)
      (show 0≤B.loU+B.side-((47/20)*B.c-(33/20)*t) by
        linarith only [marked.2.1])
    have last := mul_nonneg hp (sub_nonneg.mpr capV)
    have width := mul_nonneg hp (sub_nonneg.mpr side)
    have identity : K*((47/20)*B.c-(33/20)*t)+H*(2*B.c+3*t-1)=r*X+d*Y := by
      dsimp [K,H,X,Y]
      linear_combination ((47/20)*r+2*d)*bn.2.2
    have mixed : B.c*t≤3/10 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
      nlinarith only [product,small]
    have xBound : X≤47/20 := by
      have product := mul_nonneg bn.1
        (show 0≤1-(13/20)*t-(7/20)*B.c by linarith only [small,bb.2.1])
      dsimp [X]; nlinarith only [product]
    have yBound : Y≤13/10 := by
      dsimp [Y]; nlinarith only [mixed,wide,sq_nonneg t]
    have xWeight := mul_nonneg dn.1 (sub_nonneg.mpr xBound)
    have yWeight := mul_nonneg dp (sub_nonneg.mpr yBound)
    nlinarith only [formula,first,last,width,identity,xWeight,yWeight]

theorem support_bound (D B : OpenSquare) (r t : ℝ) {p s : ℝ}
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal p s) (dn : Normal D.c r) (bn : Normal B.c t)
    (same : D.side=B.side) (side : 1≤D.side) (small : t≤3/10)
    (steep : 47/100≤s)
    (dMarker : D.Inside 2 (457/500)) (bMarker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (outgoing : D.loV+D.side≤lower B r D.c) :
    lower D s p≤2*s+(3/5)*p := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have pp : 0≤p := by linarith only [ob.1]
  have dp : 0≤D.c := by linarith only [db.1]
  have next := neighbor_support B t bs bn dn (by simpa only [same] using side)
    small bMarker capU capV
  let P := s*D.c-p*r
  let Q := s*r+p*D.c
  have qp : 0≤Q := by
    dsimp [Q]; exact add_nonneg (mul_nonneg on.1 dn.1) (mul_nonneg pp dp)
  have marked := (negative_bands D r _ _ ds).mp dMarker
  have lowerBound : lower D s p≤P*(2*D.c-(457/500)*r)+Q*D.loV := by
    by_cases sign : 0≤P
    · have formula : lower D s p=P*D.loU+Q*D.loV :=
        lower_negative_pos D r _ _ ds sign qp
      have weight := mul_nonneg sign
        (show 0≤2*D.c-(457/500)*r-D.loU by linarith only [marked.1])
      nlinarith only [formula,weight]
    · have sign' : P≤0 := le_of_lt (lt_of_not_ge sign)
      have formula : lower D s p=P*(D.loU+D.side)+Q*D.loV :=
        lower_negative_nonpos D r _ _ ds sign' qp
      have weight := mul_nonneg (neg_nonneg.mpr sign')
        (show 0≤D.loU+D.side-(2*D.c-(457/500)*r) by linarith only [marked.2.1])
      nlinarith only [formula,weight]
  have vWeight := mul_nonneg qp
    (show 0≤(47/20)*r+(13/10)*D.c-1-D.loV by
      linarith only [next,outgoing,side])
  have identity : P*(2*D.c-(457/500)*r)+Q*((47/20)*r+(13/10)*D.c-1)=
      2*s+(457/500)*p-Q+Q*((7/20)*r+(193/500)*D.c) := by
    dsimp [P,Q]
    linear_combination (2*s+(457/500)*p)*dn.2.2
  have short : (7/20)*r+(193/500)*D.c≤11/20 := by
    nlinarith only [dn.2.2,
      sq_nonneg ((7/20)-(11/20)*r),
      sq_nonneg ((193/500)-(11/20)*D.c)]
  have shortWeight := mul_nonneg qp (sub_nonneg.mpr short)
  have rSmall : r≤5/7 := by linarith only [dn.2.1,db.2.2.2.2.2]
  have square := mul_nonneg dn.1 (sub_nonneg.mpr rSmall)
  have defect := mul_nonneg (sub_nonneg.mpr db.2.1)
    (show 0≤D.c-7/10 by linarith only [db.1])
  have chord : 1-D.c≤(3/7)*r := by
    nlinarith only [square,defect,dn.2.2,dn.1]
  have first := mul_nonneg (sub_nonneg.mpr ob.2.1) (sub_nonneg.mpr db.2.1)
  have last := mul_nonneg dn.1 (sub_nonneg.mpr steep)
  have comparison : p≤Q := by dsimp [Q]; nlinarith only [chord,first,last,dn.1]
  nlinarith only [lowerBound,vWeight,identity,shortWeight,comparison,pp]

theorem impossible (D B : OpenSquare) (r t : ℝ) {p s : ℝ}
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal p s) (dn : Normal D.c r) (bn : Normal B.c t)
    (same : D.side=B.side) (side : 1≤D.side) (small : t≤3/10)
    (steep : 47/100≤s)
    (dMarker : D.Inside 2 (457/500)) (bMarker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : boundary p s<lower D s p)
    (outgoing : D.loV+D.side≤lower B r D.c) : False := by
  have support := support_bound D B r t ds bs on dn bn same side small steep
    dMarker bMarker capU capV outgoing
  have endpoint := boundary_horizontal on
  nlinarith only [support,endpoint,incoming,on.2.1,on.1]

#print axioms support_bound
#print axioms impossible
end N12Compact.NegativeBottomOwnTransverse
