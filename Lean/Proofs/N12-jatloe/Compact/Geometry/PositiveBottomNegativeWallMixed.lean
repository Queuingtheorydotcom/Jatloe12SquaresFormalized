import Compact.Geometry.PositiveBottomNegativeWallCycle
import Compact.Geometry.PositiveBottomSupport

/-! The remaining mixed negative-wall selector uses the actual bottom
marker as well as both genuine upper faces of the central square. The
small central tilt is supplied by the original farther wall point, and
is kept explicit here. -/
namespace N12Compact.PositiveBottomNegativeWallMixed

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
set_option Elab.async false

private theorem wide {c t : ℝ} (normal : Normal c t) (small : t≤3/10) : 9/10≤c := by
  have bounds := normal_bounds normal
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤3/10+t by linarith only [normal.1])
  by_contra failure
  have compare := mul_nonneg (show 0≤9/10-c by linarith only [failure])
    (show 0≤9/10+c by linarith only [bounds.1])
  nlinarith only [square,compare,normal.2.2]

private theorem virtual_bounds {d r X Y : ℝ} (normal : Normal d r)
    (ylo : 457/500≤Y) (yhi : Y≤13/10)
    (xhi : X≤21/10 ∨ (X≤47/20 ∧ r≤3/10)) :
    2+r^2*(X-2)+d*r*(Y-457/500)-r≤2 ∧
      (2+r^2*(X-2)+d*r*(Y-457/500)-r)+
        (Y-d+d*r*(X-2)+r^2*(457/500-Y))≤5/2 := by
  have b := normal_bounds normal
  have dp : 0≤d := by linarith only [b.1]
  let U := 2+r^2*(X-2)+d*r*(Y-457/500)-r
  let V := Y-d+d*r*(X-2)+r^2*(457/500-Y)
  have negativeLast := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ylo)
  rcases xhi with xSmall | ⟨xBound,rSmall⟩
  · have xWeight := mul_nonneg normal.1 (sub_nonneg.mpr xSmall)
    have yWeight := mul_nonneg dp (sub_nonneg.mpr yhi)
    have inner : r*(X-2)+d*(Y-457/500)≤1/2 := by
      nlinarith only [xWeight,yWeight,b.2.1,b.2.2.2.1]
    have scaled := mul_nonneg normal.1 (sub_nonneg.mpr inner)
    have upperU : U≤2-r/2 := by dsimp [U]; nlinarith only [scaled]
    have product := mul_nonneg (mul_nonneg dp normal.1) (sub_nonneg.mpr xSmall)
    have shorten := mul_nonneg normal.1 (sub_nonneg.mpr b.2.1)
    have upperV : V≤13/10-d+r/10 := by
      dsimp [V]; nlinarith only [product,shorten,negativeLast,yhi]
    have diagonal : 41/50≤d+(2/5)*r := by
      linarith only [b.1,b.2.2.2.2.1]
    dsimp [U,V] at upperU upperV
    constructor <;> nlinarith only [upperU,upperV,diagonal,normal.1]
  · have dw := wide normal rSmall
    have xWeight := mul_nonneg normal.1 (sub_nonneg.mpr xBound)
    have yWeight := mul_nonneg dp (sub_nonneg.mpr yhi)
    have inner : r*(X-2)+d*(Y-457/500)≤1/2 := by
      nlinarith only [xWeight,yWeight,b.2.1,rSmall]
    have scaled := mul_nonneg normal.1 (sub_nonneg.mpr inner)
    have upperU : U≤2-r/2 := by dsimp [U]; nlinarith only [scaled]
    have product := mul_nonneg (mul_nonneg dp normal.1) (sub_nonneg.mpr xBound)
    have shorten := mul_nonneg normal.1 (sub_nonneg.mpr b.2.1)
    have upperV : V≤13/10-d+(7/20)*r := by
      dsimp [V]; nlinarith only [product,shorten,negativeLast,yhi]
    dsimp [U,V] at upperU upperV
    constructor <;> nlinarith only [upperU,upperV,dw,normal.1]

private theorem through_wall (D B : OpenSquare) (r : ℝ) {p q X Y : ℝ}
    (ds : D.s=-r) (on : Normal p q) (dn : Normal D.c r)
    (same : D.side=B.side) (side : 1≤D.side)
    (marker : D.Inside 2 (457/500))
    (outgoing : D.loV+D.side≤lower B r D.c)
    (support : lower B r D.c≤r*X+D.c*Y)
    (ylo : 457/500≤Y) (yhi : Y≤13/10)
    (xhi : X≤21/10 ∨ (X≤47/20 ∧ r≤3/10)) :
    lower D p q≤2*p+q/2 := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have pp : 0≤p := by linarith only [ob.1]
  have dp : 0≤D.c := by linarith only [db.1]
  let K := p*D.c-q*r
  let H := p*r+q*D.c
  have kp : 0≤K := by
    have first := mul_nonneg dp (sub_nonneg.mpr on.2.1)
    have last := mul_nonneg on.1 (sub_nonneg.mpr dn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg pp dn.1) (mul_nonneg on.1 dp)
  have m := (negative_bands D r _ _ ds).mp marker
  have first := mul_nonneg kp (sub_nonneg.mpr m.1.le)
  have last := mul_nonneg hp
    (show 0≤r*X+D.c*Y-1-D.loV by linarith only [outgoing,support,side])
  have formula : lower D p q=K*D.loU+H*D.loV :=
    lower_negative_pos D r _ _ ds kp hp
  let U := 2+r^2*(X-2)+D.c*r*(Y-457/500)-r
  let V := Y-D.c+D.c*r*(X-2)+r^2*(457/500-Y)
  have identity : K*(2*D.c-(457/500)*r)+H*(r*X+D.c*Y-1)=p*U+q*V := by
    dsimp [K,H,U,V]
    linear_combination (2*p+q*Y)*dn.2.2
  have bounds := virtual_bounds dn ylo yhi xhi
  have firstCone := mul_nonneg (sub_nonneg.mpr on.2.1)
    (sub_nonneg.mpr bounds.1)
  have lastCone := mul_nonneg on.1 (sub_nonneg.mpr bounds.2)
  dsimp [U,V] at identity
  clear_value K H U V
  nlinarith only [formula,first,last,identity,firstCone,lastCone]

/-- The actual bottom marker and complete central square upper faces
bound the preceding support in every positive canonical direction. -/
theorem support_bound (D B : OpenSquare) (r t : ℝ) {p q : ℝ}
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal p q) (dn : Normal D.c r) (bn : Normal B.c t)
    (same : D.side=B.side) (side : 1≤D.side) (small : t≤3/10)
    (dMarker : D.Inside 2 (457/500)) (bMarker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (outgoing : D.loV+D.side≤lower B r D.c) :
    lower D p q≤2*p+q/2 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0≤D.c := by linarith only [db.1]
  have bp : 0≤B.c := by linarith only [bb.1]
  have bWide := wide bn small
  have bSide : 1≤B.side := by simpa only [same] using side
  let K := r*B.c-D.c*t
  let H := r*t+D.c*B.c
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg dn.1 bn.1) (mul_nonneg dp bp)
  by_cases order : t≤r
  · have cosine := cosine_order dn bn order
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg bp (sub_nonneg.mpr order)
    have kp : 0≤K := by dsimp [K]; nlinarith only [first,last]
    let X := 3+B.c*t-B.c-t
    let Y := 2-t^2+t-B.c
    have formula : lower B r D.c=K*B.loU+H*B.loV :=
      lower_negative_pos B t _ _ bs kp hp
    have uWeight := mul_nonneg kp (sub_nonneg.mpr capU)
    have vWeight := mul_nonneg hp (sub_nonneg.mpr capV)
    have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr bSide)
    have identity : K*(3*B.c-t-1)+H*(2*B.c+3*t-1)=r*X+D.c*Y := by
      dsimp [K,H,X,Y]
      linear_combination (3*r+2*D.c)*bn.2.2
    have bound : lower B r D.c≤r*X+D.c*Y := by
      nlinarith only [formula,uWeight,vWeight,width,identity]
    have xBound : X≤21/10 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
      dsimp [X]; nlinarith only [bWide,product]
    have yLower : 1≤Y := by
      have square := sq_nonneg (1-B.c)
      dsimp [Y]
      nlinarith only [bn.2.2,bb.2.2.2.2.1,square]
    have yBound : Y≤13/10 := by
      have product := mul_nonneg bp (sub_nonneg.mpr bb.2.1)
      dsimp [Y]; nlinarith only [bn.2.2,small,product]
    exact through_wall D B r ds on dn same side dMarker outgoing bound
      (by clear_value Y; linarith only [yLower]) yBound (Or.inl xBound)
  · have order' : r≤t := le_of_not_ge order
    have cosine := cosine_order bn dn order'
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg bp (sub_nonneg.mpr order')
    have kn : K≤0 := by dsimp [K]; nlinarith only [first,last]
    let X := 47/20+(13/20)*t^2+(7/20)*B.c*t-t
    let Y := 2-(7/20)*t^2+(13/20)*B.c*t-B.c
    have formula : lower B r D.c=K*(B.loU+B.side)+H*B.loV := by
      exact lower_negative_nonpos B t _ _ bs kn hp
    have marker := (negative_bands B t _ _ bs).mp bMarker
    have uWeight := mul_nonneg (neg_nonneg.mpr kn)
      (show 0≤B.loU+B.side-((47/20)*B.c-(33/20)*t) by linarith only [marker.2.1])
    have vWeight := mul_nonneg hp (sub_nonneg.mpr capV)
    have width := mul_nonneg hp (sub_nonneg.mpr bSide)
    have identity : K*((47/20)*B.c-(33/20)*t)+H*(2*B.c+3*t-1)=r*X+D.c*Y := by
      dsimp [K,H,X,Y]
      linear_combination ((47/20)*r+2*D.c)*bn.2.2
    have bound : lower B r D.c≤r*X+D.c*Y := by
      clear_value K H X Y
      nlinarith only [formula,uWeight,vWeight,width,identity]
    have mixed : B.c*t≤3/10 := by
      have product := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
      nlinarith only [product,small]
    have tSquare : t^2≤9/100 := by
      have product := mul_nonneg (sub_nonneg.mpr small)
        (show 0≤3/10+t by linarith only [bn.1])
      nlinarith only [product]
    have xBound : X≤47/20 := by
      have product := mul_nonneg bn.1
        (show 0≤1-(13/20)*t-(7/20)*B.c by linarith only [bb.2.1,small])
      dsimp [X]; nlinarith only [product]
    have yLower : 457/500≤Y := by
      have product := mul_nonneg bp bn.1
      dsimp [Y]; nlinarith only [tSquare,product,bb.2.1]
    have yBound : Y≤13/10 := by
      dsimp [Y]; nlinarith only [mixed,bWide,sq_nonneg t]
    exact through_wall D B r ds on dn same side dMarker outgoing bound yLower yBound
      (Or.inr ⟨xBound,le_trans order' small⟩)

/-- The preceding actual singleton is wider than the support budget
left by the wall and central square, closing this complete selector. -/
theorem own_wall_transverse (O D B : OpenSquare) (r t : ℝ)
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal O.c O.s) (dn : Normal D.c r) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side)
    (side : 1<D.side) (small : t≤3/10)
    (oFloor : 0≤O.s*O.loU+O.c*O.loV)
    (oCap : O.loV+O.side≤O.c-O.s)
    (dMarker : D.Inside 2 (457/500)) (bMarker : B.Inside (47/20) (33/20))
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : O.loU+O.side≤lower D O.c O.s)
    (outgoing : D.loV+D.side≤lower B r D.c) : False := by
  have first := PositiveBottomSupport.own_axis O on
    (by simpa only [sameOD] using side) oCap oFloor
  have last := support_bound D B r t ds bs on dn bn sameDB side.le small
    dMarker bMarker capU capV outgoing
  linarith only [first,last,incoming]

end N12Compact.PositiveBottomNegativeWallMixed
