import Compact.Geometry.PositiveBottomWallCentralAxis

/-! The negative bottom singleton's upward separator cannot be followed
by the central neighbor's transverse separator. The true wall floor and
the original extended point at 2.6 retain the two sides of the relative
angle order. No upper bound on the singleton's tilt is required. -/
namespace N12Compact.NegativeBottomWallCentralAxis

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem arc {p q : ℝ} (normal : Normal p q) :
    1+(4/5)*p*q≤p+q := by
  have b := normal_bounds normal
  have pp : 0≤p := by linarith only [b.1]
  have product := mul_nonneg (mul_nonneg pp normal.1)
    (show 0≤6/5-(4/5)*(p+q) by linarith only [b.2.2.2.2.2])
  have identity : (p+q+1)*(p+q-1-(4/5)*p*q)=
      p*q*(6/5-(4/5)*(p+q)) := by
    linear_combination normal.2.2
  have scaled : 0≤(p+q+1)*(p+q-1-(4/5)*p*q) := by
    linarith only [identity,product]
  have gap := nonneg_of_mul_nonneg_right scaled
    (show 0<p+q+1 by linarith only [b.2.2.2.2.1])
  linarith only [gap]

/-- A uniform lower bound for the actual negative singleton's upper V
face follows from its corner face and full bottom containment. -/
theorem singleton_height (O : OpenSquare) (q : ℝ)
    (on : Normal O.c q) (side : 1<O.side)
    (corner : O.c-q≤O.loU)
    (floor : q*(O.loU+O.side)≤O.c*O.loV) :
    O.c+(9/5)*q<O.loV+O.side := by
  have b := normal_bounds on
  have cp : 0<O.c := by linarith only [b.1]
  have first := mul_nonneg on.1 (sub_nonneg.mpr corner)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<O.c+q by linarith only [b.2.2.2.2.1])
  have circleArc := arc on
  have identity : O.c*(O.loV+O.side-(O.c+(9/5)*q))=
      (O.c*O.loV-q*(O.loU+O.side))+q*(O.loU-(O.c-q))+
      (O.side-1)*(O.c+q)+(O.c+q-1-(4/5)*O.c*q) := by
    linear_combination -on.2.2
  have strict : 0<O.c*(O.loV+O.side-(O.c+(9/5)*q)) := by
    nlinarith only [identity,floor,first,width,circleArc]
  have gap := pos_of_mul_pos_right strict cp.le
  linarith only [gap]

private theorem support_width {d r c t : ℝ}
    (dn : Normal d r) (bn : Normal c t) :
    c+(2/5)*t≤(t*d+c*r)+(c*d-t*r) := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have first := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤d+r-1 by linarith only [db.2.2.2.2.1])
  have last := mul_nonneg bn.1
    (show 0≤2*d-7/5 by linarith only [db.1])
  nlinarith only [first,last]

private theorem horizontal_margin {d r c t : ℝ}
    (dn : Normal d r) (bn : Normal c t) :
    0≤d+c*d*(d+r-1)+t*(d*(d-r-2/5)-1) := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0≤d := by linarith only [db.1]
  have first := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (mul_nonneg dp (show 0≤d+r-1 by linarith only [db.2.2.2.2.1]))
  let K := 2*d^2-(7/5)*d-1
  have dSquare := mul_nonneg dp (sub_nonneg.mpr db.2.1)
  have kn : K≤0 := by dsimp [K]; nlinarith only [dSquare,db.2.1]
  have small : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
  have last := mul_nonneg (sub_nonneg.mpr small) (neg_nonneg.mpr kn)
  have order := mul_nonneg (sub_nonneg.mpr dn.2.1) (add_nonneg dp dn.1)
  have square : 0≤2*d^2-1 := by nlinarith only [order,dn.2.2]
  dsimp [K] at last
  nlinarith only [first,last,square]

theorem own_transverse (O D B : OpenSquare) (q t : ℝ)
    (on : Normal O.c q) (dn : Normal D.c D.s) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side)
    (side : 1<D.side) (tilt : 0<q)
    (corner : O.c-q≤O.loU)
    (bottom : q*(O.loU+O.side)≤O.c*O.loV)
    (box : InsideContainer D) (high : D.Inside (13/5) 1)
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : O.loV+O.side≤lower D q O.c)
    (outgoing : upper D t B.c≤B.loV) : False := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have op : 0<O.c := by linarith only [ob.1]
  have dp : 0<D.c := by linarith only [db.1]
  have bc : 0≤B.c := by linarith only [bb.1]
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dp.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  have oSide : 1<O.side := by simpa only [sameOD] using side
  have height := singleton_height O q on oSide corner bottom
  let K := q*D.c+O.c*D.s
  let H := O.c*D.c-q*D.s
  let P := t*D.c+B.c*D.s
  let Q := B.c*D.c-t*D.s
  let J := q*B.c-O.c*t
  have kp : 0≤K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg on.1 dp.le) (mul_nonneg op.le dn.1)
  have hp : 0≤H := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr on.2.1)
    have last := mul_nonneg on.1 (sub_nonneg.mpr dn.2.1)
    dsimp [H]; nlinarith only [first,last]
  have pp : 0≤P := by
    dsimp [P]
    exact add_nonneg (mul_nonneg bn.1 dp.le) (mul_nonneg bc dn.1)
  have qp : 0≤Q := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [Q]; nlinarith only [first,last]
  have upperFormula : upper D t B.c=P*(D.loU+D.side)+Q*(D.loV+D.side) := by
    rw [upper_in_bands]
    have u : t*D.c+B.c*D.s=P := rfl
    have v : -t*D.s+B.c*D.c=Q := by dsimp [Q]; ring
    rw [u,v,abs_of_nonneg pp,abs_of_nonneg qp]; ring
  have lowerFormula : lower D q O.c=K*D.loU+H*D.loV := by
    rw [lower_in_bands]
    have u : q*D.c+O.c*D.s=K := rfl
    have v : -q*D.s+O.c*D.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonneg hp]; ring
  have exit : upper D t B.c+D.side≤2*B.c+3*t := by
    rw [←sameDB] at cap
    linarith only [outgoing,cap]
  have entry : O.c+(9/5)*q≤lower D q O.c := by
    linarith only [height,incoming]
  have supportWidth : B.c+(2/5)*t≤P+Q := support_width dn bn
  by_cases order : 0≤J
  · have first := mul_nonneg bn.1 (sub_nonneg.mpr entry)
    have floorWeight := mul_nonneg order wall
    have width := mul_pos (sub_pos.mpr side)
      (mul_pos tilt (show 0<1+P+Q by linarith only [pp,qp]))
    have widthWeight := mul_nonneg on.1 (sub_nonneg.mpr supportWidth)
    have defect := mul_nonneg on.1 (sub_nonneg.mpr bb.2.1)
    have angleWeight := mul_nonneg bn.1
      (show 0≤O.c-(4/5)*q by linarith only [on.2.1,on.1])
    have residual : 0≤t*(O.c+(9/5)*q)+q*(1+P+Q-2*B.c-3*t) := by
      nlinarith only [widthWeight,defect,angleWeight]
    have identity : q*(upper D t B.c+D.side-(2*B.c+3*t))=
        t*(lower D q O.c-(O.c+(9/5)*q))+J*(D.s*D.loU+D.c*D.loV)+
        (D.side-1)*q*(1+P+Q)+
        (t*(O.c+(9/5)*q)+q*(1+P+Q-2*B.c-3*t)) := by
      rw [upperFormula,lowerFormula]
      dsimp [K,H,P,Q,J]; ring
    have limit := mul_nonneg on.1 (sub_nonneg.mpr exit)
    clear_value K H P Q J
    nlinarith only [identity,first,floorWeight,width,residual,limit]
  · have jn : J<0 := lt_of_not_ge order
    have tp : 0<t := by
      have first := mul_nonneg on.1 bc
      dsimp [J] at jn
      nlinarith only [jn,first,op]
    have strictAngle : q<O.c := by
      apply lt_of_not_ge
      intro failure
      have equal : O.c=q := by linarith only [failure,on.2.1]
      have first := mul_nonneg on.1 (sub_nonneg.mpr bn.2.1)
      dsimp [J] at jn
      rw [equal] at jn
      nlinarith only [jn,first]
    have hPositive : 0<H := by
      have first := mul_pos dp (sub_pos.mpr strictAngle)
      have last := mul_nonneg on.1 (sub_nonneg.mpr dn.2.1)
      dsimp [H]; nlinarith only [first,last]
    let Fh := D.c+B.c*D.c*(D.c+D.s-1)+
      t*(D.c*(D.c-D.s-2/5)-1)
    let Fp := Q*(1-B.c-(6/5)*t+P+Q)
    let F := Q*(O.c+(9/5)*q)-J*((13/5)*D.c+D.s-1)+
      H*(1+P+Q-2*B.c-3*t)
    have horizontal : 0≤Fh := horizontal_margin dn bn
    have parallel : 0≤Fp := by
      have baseline : 0≤1-(4/5)*t := by linarith only [bb.2.2.2.1]
      have bracket : 0≤1-B.c-(6/5)*t+P+Q := by
        linarith only [supportWidth,baseline]
      exact mul_nonneg qp bracket
    have firstEndpoint := mul_nonneg (neg_nonneg.mpr jn.le) horizontal
    have lastEndpoint := mul_nonneg on.1 parallel
    have cone : t*F=(-J)*Fh+q*Fp := by
      dsimp [F,Fh,Fp,J,H,P,Q]
      ring
    have scalar : 0≤F := by
      have scaled : 0≤t*F := by linarith only [cone,firstEndpoint,lastEndpoint]
      exact nonneg_of_mul_nonneg_right scaled tp
    let G := H*(1+P+Q)+J
    have gp : 0<G := by
      have first := mul_pos hPositive (show 0<1+Q by linarith only [qp])
      have last := mul_nonneg qp kp
      have identity : G=H*(1+Q)+Q*K := by
        dsimp [G,J,H,P,Q,K]
        linear_combination -(q*B.c-O.c*t)*dn.2.2
      linarith only [identity,first,last]
    have entryWeight := mul_nonneg qp (sub_nonneg.mpr entry)
    have highWeight := mul_nonneg (neg_nonneg.mpr jn.le)
      (show 0≤D.loU+D.side-((13/5)*D.c+D.s) by linarith only [high.2.1])
    have width := mul_pos (sub_pos.mpr side) gp
    have identity : H*(upper D t B.c+D.side-(2*B.c+3*t))=
        Q*(lower D q O.c-(O.c+(9/5)*q))+
        (-J)*(D.loU+D.side-((13/5)*D.c+D.s))+(D.side-1)*G+F := by
      rw [upperFormula,lowerFormula]
      dsimp [G,F,J,H,P,Q,K]
      linear_combination -(q*B.c-O.c*t)*D.loU*dn.2.2
    have limit := mul_nonneg hp (sub_nonneg.mpr exit)
    clear_value K H P Q J Fh Fp F G
    nlinarith only [identity,entryWeight,highWeight,width,scalar,limit]

#print axioms singleton_height
#print axioms own_transverse
end N12Compact.NegativeBottomWallCentralAxis
