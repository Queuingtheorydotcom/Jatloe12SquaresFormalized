import Compact.Geometry.CentralNegativeBottomAxes

/-! One complete selector of the negative bottom-wall chain. The true
singleton far point gives D's lower face; both relative angles of the
negative wall and negative central neighbor are included. -/
namespace N12Compact.NegativeBottomTransverseChain

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
set_option Elab.async false

private theorem first_margin {c t d r : ℝ} (bn : Normal c t) (dn : Normal d r)
    (small : t≤3/10) :
    0<1+c*(d-31/25+(77/500)*r^2-(13/100)*d*r)+
      t*(r-1-(13/100)*r^2-(77/500)*d*r) := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have mixed : d*r≤1/2 := by nlinarith only [dn.2.2,sq_nonneg (d-r)]
  have first : -(121/200)≤d-31/25+(77/500)*r^2-(13/100)*d*r := by
    nlinarith only [db.1,mixed,sq_nonneg r]
  have factor : 0≤1-(13/100)*r-(77/500)*d := by
    linarith only [db.2.1,db.2.2.2.1]
  have product := mul_nonneg dn.1 factor
  have last : -1≤r-1-(13/100)*r^2-(77/500)*d*r := by nlinarith only [product]
  have firstWeight := mul_nonneg (show 0≤c by linarith only [bb.1]) (sub_nonneg.mpr first)
  have lastWeight := mul_nonneg bn.1 (sub_nonneg.mpr last)
  nlinarith only [firstWeight,lastWeight,bb.2.1,small]

private theorem last_margin {c t d r : ℝ} (bn : Normal c t) (dn : Normal d r)
    (small : t≤3/10) (order : r≤t) :
    0<1+c*(d-31/25+(6/25)*r^2-(99/100)*d*r)+
      t*(r-7/50-(99/100)*r^2-(6/25)*d*r) := by
  have bb := normal_bounds bn
  have db := normal_bounds dn
  have little : r≤3/10 := le_trans order small
  have square := mul_self_le_mul_self dn.1 little
  have wide : 9/10≤d := by nlinarith only [square,dn.2.2,db.1]
  have product := mul_nonneg dn.1 (sub_nonneg.mpr db.2.1)
  have mixed : d*r≤3/10 := by nlinarith only [product,little]
  have first : -(637/1000)≤d-31/25+(6/25)*r^2-(99/100)*d*r := by
    nlinarith only [wide,mixed,sq_nonneg r]
  have factor : 0≤1-(99/100)*r-(6/25)*d := by linarith only [little,db.2.1]
  have product := mul_nonneg dn.1 factor
  have last : -(7/50)≤r-7/50-(99/100)*r^2-(6/25)*d*r := by nlinarith only [product]
  have firstWeight := mul_nonneg (show 0≤c by linarith only [bb.1]) (sub_nonneg.mpr first)
  have lastWeight := mul_nonneg bn.1 (sub_nonneg.mpr last)
  nlinarith only [firstWeight,lastWeight,bb.2.1,small]

/-- O/D on D's V axis followed by D/B on B's V axis is impossible.
O's orientation is unrestricted; its actual far point is used strictly. -/
theorem impossible (O D B : OpenSquare) (r t : ℝ)
    (dn : Normal D.c r) (bn : Normal B.c t) (ds : D.s=-r)
    (same : D.side=B.side) (side : 1<B.side) (small : t≤3/10)
    (far : O.Inside (187/100) (19/25))
    (marker : D.Inside 2 (457/500)) (high : D.Inside (143/50) 1)
    (incoming : upper O r D.c≤D.loV)
    (outgoing : upper D t B.c≤B.loV)
    (cap : B.loV+B.side≤2*B.c+3*t) : False := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have point := strict_bounds O _ _ r D.c (by nlinarith only [dn.2.2]) far
  have floor : (187/100)*r+(19/25)*D.c<D.loV := by linarith only [point.2,incoming]
  have marked := (negative_bands D r _ _ ds).mp marker
  have farthest := (negative_bands D r _ _ ds).mp high
  let P := t*D.c-B.c*r
  let Q := t*r+B.c*D.c
  have qp : 0<Q := by
    have product := mul_nonneg bn.1 dn.1
    have strict := mul_pos bc dc
    dsimp [Q]; linarith only [product,strict]
  by_cases order : t≤r
  · have cosine := cosine_order dn bn order
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg bc.le (sub_nonneg.mpr order)
    have pn : P≤0 := by dsimp [P]; nlinarith only [first,last]
    have formula : upper D t B.c=P*D.loU+Q*(D.loV+D.side) := by
      rw [upper_in_bands,ds]
      have u : t*D.c+B.c*(-r)=P := by dsimp [P]; ring
      have v : -t*(-r)+B.c*D.c=Q := by dsimp [Q]; ring
      rw [u,v,abs_of_nonpos pn,abs_of_nonneg qp.le]; ring
    have markerWeight := mul_nonneg (neg_nonneg.mpr pn)
      (show 0≤2*D.c-(457/500)*r-D.loU by linarith only [marked.1])
    have floorWeight := mul_pos qp (sub_pos.mpr floor)
    have width := mul_pos (show 0<1+Q by linarith only [qp]) (sub_pos.mpr side)
    have identity : P*(2*D.c-(457/500)*r)+
        Q*((187/100)*r+(19/25)*D.c+1)+1-2*B.c-3*t=
        1+B.c*(D.c-31/25+(77/500)*r^2-(13/100)*D.c*r)+
          t*(r-1-(13/100)*r^2-(77/500)*D.c*r) := by
      dsimp [P,Q]
      linear_combination ((19/25)*B.c+2*t)*dn.2.2
    have margin := first_margin bn dn small
    rw [same] at formula
    clear_value P Q
    nlinarith only [formula,markerWeight,floorWeight,width,identity,margin,outgoing,cap]
  · have order' : r≤t := le_of_lt (lt_of_not_ge order)
    have cosine := cosine_order bn dn order'
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg bc.le (sub_nonneg.mpr order')
    have pp : 0≤P := by dsimp [P]; nlinarith only [first,last]
    have formula : upper D t B.c=P*(D.loU+D.side)+Q*(D.loV+D.side) := by
      rw [upper_in_bands,ds]
      have u : t*D.c+B.c*(-r)=P := by dsimp [P]; ring
      have v : -t*(-r)+B.c*D.c=Q := by dsimp [Q]; ring
      rw [u,v,abs_of_nonneg pp,abs_of_nonneg qp.le]; ring
    have highWeight := mul_nonneg pp
      (show 0≤D.loU+D.side-((143/50)*D.c-r) by linarith only [farthest.2.1])
    have floorWeight := mul_pos qp (sub_pos.mpr floor)
    have width := mul_pos (show 0<1+Q by linarith only [qp]) (sub_pos.mpr side)
    have identity : P*((143/50)*D.c-r)+
        Q*((187/100)*r+(19/25)*D.c+1)+1-2*B.c-3*t=
        1+B.c*(D.c-31/25+(6/25)*r^2-(99/100)*D.c*r)+
          t*(r-7/50-(99/100)*r^2-(6/25)*D.c*r) := by
      dsimp [P,Q]
      linear_combination ((19/25)*B.c+(143/50)*t)*dn.2.2
    have margin := last_margin bn dn small order'
    rw [same] at formula highWeight
    clear_value P Q
    nlinarith only [formula,highWeight,floorWeight,width,identity,margin,outgoing,cap]

#print axioms impossible
end N12Compact.NegativeBottomTransverseChain
