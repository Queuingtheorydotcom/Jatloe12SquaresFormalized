import Compact.Geometry.CentralNegativeBottomAxes
import Compact.Geometry.OwnedWestBottomAngle

/-! A steep negative bottom singleton cannot pass its upper transverse
face through a negative bottom wall whose upper support lies below the
negative central neighbor. The neighbor's genuine farther-point bound
enters only through its small tilt. Both relative wall angles are kept. -/
namespace N12Compact.NegativeBottomCentralAxis

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

/-- The wall's actual marker and the outgoing central axis bound its
lower support in the steep singleton direction by the point `(2,.6)`.
This is a consequence of the full outgoing support, not a container
replacement for the wall. -/
theorem support_bound (D B : OpenSquare) (r t p s : ℝ)
    (ds : D.s=-r) (dn : Normal D.c r) (bn : Normal B.c t)
    (on : Normal p s) (steep : 47/100<s) (small : t≤3/10)
    (same : D.side=B.side) (side : 1≤B.side)
    (marker : D.Inside 2 (457/500))
    (outgoing : upper D t B.c≤B.loV)
    (cap : B.loV+B.side≤2*B.c+3*t) :
    lower D s p≤2*s+(3/5)*p := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have ob := normal_bounds on
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have pc : 0≤p := by linarith only [ob.1]
  have wide : 9/10≤B.c := by
    have square := mul_self_le_mul_self bn.1 small
    nlinarith only [square,bn.2.2,bb.1]
  let P := t*D.c-B.c*r
  let Q := t*r+B.c*D.c
  let H := s*D.c-p*r
  let K := s*r+p*D.c
  let J := s*B.c-p*t
  have qp : 0<Q := by
    have first := mul_nonneg bn.1 dn.1
    have last := mul_pos bc dc
    dsimp [Q]; linarith only [first,last]
  have kp : 0≤K := by dsimp [K]; positivity
  have jp : 0≤J := by
    have first := mul_nonneg on.1 (sub_nonneg.mpr wide)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr ob.2.1)
    dsimp [J]; nlinarith only [first,last,steep,small]
  have outBound : P*D.loU+Q*(D.loV+D.side)≤upper D t B.c := by
    rw [upper_in_bands,ds]
    have u : t*D.c+B.c*(-r)=P := by dsimp [P]; ring
    have v : -t*(-r)+B.c*D.c=Q := by dsimp [Q]; ring
    rw [u,v,abs_of_nonneg qp.le]
    by_cases sign : 0≤P
    · rw [abs_of_nonneg sign]
      have extra := mul_nonneg sign D.side_pos.le
      nlinarith only [extra]
    · rw [abs_of_nonpos (le_of_not_ge sign)]
      nlinarith only []
  have inBound : lower D s p≤H*D.loU+K*D.loV := by
    rw [lower_in_bands,ds]
    have u : s*D.c+p*(-r)=H := by dsimp [H]; ring
    have v : -s*(-r)+p*D.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg kp]
    by_cases sign : 0≤H
    · rw [abs_of_nonneg sign]
      nlinarith only []
    · rw [abs_of_nonpos (le_of_not_ge sign)]
      have extra := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge sign) D.side_pos.le
      nlinarith only [extra]
  have marked := (negative_bands D r _ _ ds).mp marker
  have outgoingWeight := mul_nonneg kp
    (show 0≤B.loV-upper D t B.c by linarith only [outgoing])
  have supportWeight := mul_nonneg kp (sub_nonneg.mpr outBound)
  have capWeight := mul_nonneg kp (sub_nonneg.mpr cap)
  have inWeight := mul_nonneg qp.le (sub_nonneg.mpr inBound)
  have markerWeight := mul_nonneg jp
    (show 0≤2*D.c-(457/500)*r-D.loU by linarith only [marked.1])
  have widthWeight := mul_nonneg
    (show 0≤K*(1+Q) by nlinarith only [kp,qp,mul_nonneg kp qp.le])
    (sub_nonneg.mpr side)
  have dot : Q*H-K*P=J := by
    dsimp [Q,H,K,P,J]
    linear_combination (s*B.c-p*t)*dn.2.2
  rw [same] at outBound supportWeight
  have bound : Q*lower D s p≤
      J*(2*D.c-(457/500)*r)+K*(2*B.c+3*t-1-Q) := by
    have identity : Q*(H*D.loU+K*D.loV)=
        J*D.loU+K*(P*D.loU+Q*(D.loV+B.side))-K*Q*B.side := by
      linear_combination D.loU*dot
    nlinarith only [outgoingWeight,supportWeight,capWeight,inWeight,
      markerWeight,widthWeight,identity]
  have first : B.c*(543/500-D.c)+t*(1-r)-1≤0 := by
    have cosine := mul_nonneg (sub_nonneg.mpr bb.2.1)
      (show 0≤543/500-D.c by linarith only [db.2.1])
    have sine := mul_nonneg bn.1 dn.1
    nlinarith only [cosine,sine,db.1,small]
  have second : B.c*(7/5-D.c)+t-1≤0 := by
    have cosine := mul_nonneg (sub_nonneg.mpr bb.2.1)
      (show 0≤7/5-D.c by linarith only [db.2.1])
    nlinarith only [cosine,db.1,small]
  have third : 157/500-D.c≤0 := by linarith only [db.1]
  have firstWeight := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg on.1 dn.1) first
  have secondWeight := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg pc dc.le) second
  have thirdWeight := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg pc bn.1) dn.1) third
  have identity : J*(2*D.c-(457/500)*r)+K*(2*B.c+3*t-1-Q)-
      Q*(2*s+(3/5)*p)=
      s*r*(B.c*(543/500-D.c)+t*(1-r)-1)+
      p*D.c*(B.c*(7/5-D.c)+t-1)+p*t*r*(157/500-D.c) := by
    dsimp [J,K,Q]
    ring
  have scaled : Q*(lower D s p-(2*s+(3/5)*p))≤0 := by
    nlinarith only [bound,identity,firstWeight,secondWeight,thirdWeight]
  have gap := nonpos_of_mul_nonpos_right scaled qp
  linarith only [gap]

/-- The true negative-singleton boundary is strictly above `(2,.6)`
in its own transverse direction over the entire canonical arc. -/
theorem boundary_margin {p s : ℝ} (on : Normal p s) :
    2*s+(3/5)*p<boundary p s := by
  have ob := normal_bounds on
  have pp : 0<p := by linarith only [ob.1]
  have sine : s≤5/7 := by linarith only [on.2.1,ob.2.2.2.2.2]
  have positive := mul_pos
    (show 0<1-s by linarith only [sine])
    (show 0<p+(2/5)*s-3/5 by linarith only [ob.1,on.1])
  have exactBoundary : p*boundary p s=p+p*s+s-s^2 := by
    unfold boundary
    field_simp [pp.ne']
    ring
  have identity : p*(boundary p s-(2*s+(3/5)*p))=
      (1-s)*(p+(2/5)*s-3/5) := by
    nlinarith only [exactBoundary,on.2.2]
  have gap := pos_of_mul_pos_right (show 0<p*(boundary p s-(2*s+(3/5)*p)) by
    rw [identity]; exact positive) pp.le
  linarith only [gap]

/-- Complete negative O.V / negative B.V selector, with the full middle
square and both of its relative support-angle cases retained. -/
theorem impossible (O D B : OpenSquare) (s r t : ℝ)
    (on : Normal O.c s) (dn : Normal D.c r) (bn : Normal B.c t)
    (ds : D.s=-r) (same : D.side=B.side) (side : 1≤B.side)
    (steep : 47/100<s) (small : t≤3/10)
    (marker : D.Inside 2 (457/500))
    (face : boundary O.c s<O.loV+O.side)
    (incoming : O.loV+O.side≤lower D s O.c)
    (outgoing : upper D t B.c≤B.loV)
    (cap : B.loV+B.side≤2*B.c+3*t) : False := by
  have bound := support_bound D B r t O.c s ds dn bn on steep small same side
    marker outgoing cap
  have gap := boundary_margin on
  linarith only [bound,gap,face,incoming]

#print axioms impossible
end N12Compact.NegativeBottomCentralAxis
