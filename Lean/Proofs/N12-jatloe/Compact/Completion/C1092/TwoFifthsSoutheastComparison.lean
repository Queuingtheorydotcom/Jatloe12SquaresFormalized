import Compact.Completion.C1092.TwoFifthsSupport
import Compact.Completion.C1092.TwoFifthsSoutheastScalars

/-! The southeast square forces the canonical right slope below 2/5.
Both signs use the full actual square and all directed face sources.
The coupled southeast floor is kept in the positive own-right source. -/
namespace N12Compact.C1092TwoFifths
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports Support Scalars
open C1092WallProfileScalars
set_option Elab.async false
noncomputable section

private theorem south_faces (E : OpenSquare) (h : Southeast E) :
    E.loU<0 ∧ -(13/50)*E.s<E.loV+E.side ∧
      E.side-half E.c E.s<E.loU+E.side ∧
      1-half E.c E.s<E.loU+E.side := by
  have b := south_bounds E.c E.s h.cosine h.sine h.small E.unit_normal
  have hterm := mul_nonpos_of_nonneg_of_nonpos h.cosine.le h.upperV
  have strict := mul_pos (sub_pos.mpr h.side) h.cosine
  have weighted : 0<E.s*(E.loU+E.side-(E.side-half E.c E.s)) := by
    nlinarith only [h.floor,hterm,strict,b.circle]
  have bound := sub_pos.mp (pos_of_mul_pos_right weighted h.sine.le)
  refine ⟨?_,?_,bound,by linarith only [bound,h.side]⟩
  · have first := h.inner.1
    have positive := mul_pos (by norm_num : (0:ℝ)<13/50) h.sine
    nlinarith only [first,positive]
  · have point := h.forward.2.2.2
    nlinarith only [point]

private theorem south_transverse_blocked (E R : OpenSquare)
    (h : Southeast E) (right : Right R)
    (sep : upper E E.s (-E.c)≤lower R E.s (-E.c)) : False := by
  have unit : E.s^2+(-E.c)^2=1 := by nlinarith only [E.unit_normal]
  have first := (strict_bounds E 0 (-13/50) E.s (-E.c) unit h.inner).2
  have last := (strict_bounds R 1 (2/5) E.s (-E.c) unit
    (right.bar _ (by norm_num) (by norm_num))).1
  nlinarith only [first,last,sep,h.small,h.cosine]

/-- A nonpositive right frame. Its magnitude r is allowed to be zero. -/
theorem southeast_negative_small (E R : OpenSquare) (r : ℝ)
    (h : Southeast E) (right : Right R) (same : E.side=R.side)
    (frame : R.s=-r) (normal : Normal R.c r)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) : r<(2/5)*R.c := by
  let c := E.c
  let s := E.s
  let d := R.c
  let z := half c s
  let A := E.loU+E.side
  let H := E.loV+E.side
  let k := c*d-s*r
  let q := s*d+c*r
  have b := south_bounds c s h.cosine h.sine h.small E.unit_normal
  have rb := normal_bounds normal
  have dp : 0<d := by dsimp [d]; linarith only [rb.1]
  have faces := south_faces E h
  have A0 : 1-z<A := faces.2.2.2
  have H0 : -(13/50)*s<H := faces.2.1
  have kp : 0<k := by
    have first := mul_pos (show 0<c-s by linarith only [h.small,h.sine]) dp
    have last := mul_nonneg h.sine.le (sub_nonneg.mpr normal.2.1)
    dsimp [k,c,s,d] at *
    nlinarith only [first,last]
  have qp : 0<q := by
    have first := mul_pos h.sine dp
    have last := mul_nonneg h.cosine.le normal.1
    dsimp [q,c,s,d] at *
    nlinarith only [first,last]
  have L : R.loU<d-(2/5)*r := by
    have point := (right.bar (2/5) (by norm_num) (by norm_num)).1
    rw [frame] at point
    dsimp [d]
    nlinarith only [point]
  have K : R.loV<r-(13/50)*d := by
    have point := (right.bar (-13/50) (by norm_num) (by norm_num)).2.2.1
    rw [frame] at point
    dsimp [d]
    nlinarith only [point]
  have axes := negative_axes E R same h.cosine h.sine.le dp
    (by rw [frame]; linarith only [normal.1]) (13/50) 0 h.forward
    (right.bar 0 (by norm_num) (by norm_num)) (by norm_num) apart
  apply lt_of_not_ge
  intro large
  rcases axes with own|transverse|wallU|wallV
  · have formula : lower R c s=k*R.loU+q*R.loV := by
      apply lower_nn R c s k q
      · rw [frame]; dsimp [c,s,d,k]; ring
      · rw [frame]; dsimp [c,s,d,q]; ring
      · exact kp.le
      · exact qp.le
    have first := mul_lt_mul_of_pos_left L kp
    have last := mul_lt_mul_of_pos_left K qp
    have identity : k*(d-(2/5)*r)+q*(r-(13/50)*d)=
        c-(33/50)*c*d*r-s*((13/50)*d^2-(2/5)*r^2) := by
      dsimp [k,q]
      linear_combination c*normal.2.2
    have loss := negative_loss c s z d r b normal large
    have eta : c-1+z=z*(1-s) := by nlinarith only [b.circle]
    change A≤lower R c s at own
    nlinarith only [own,A0,formula,first,last,identity,loss,b.eta,eta]
  · exact south_transverse_blocked E R h right transverse
  · have formula : upper E R.c R.s=k*A-q*(H-E.side) := by
      have exactSupport := upper_pos_neg E R.c R.s k (-q)
        (by rw [frame]; dsimp [c,s,d,k]; ring)
        (by rw [frame]; dsimp [c,s,d,q]; ring) kp.le (by linarith only [qp])
      rw [exactSupport]
      dsimp [A,H]
      ring
    have first := mul_pos kp (show 0<A-(1-z) by linarith only [A0])
    have last := mul_nonneg qp.le
      (show 0≤E.side-H-1 by dsimp [H]; linarith only [h.side,h.upperV])
    have identity : k*(1-z)+q-d=(1-s)*(d*z+r) := by
      dsimp [k,q]
      linear_combination (d+r)*b.circle-d*b.relation
    have positive := mul_pos (show 0<1-s by linarith only [b.sineUpper])
      (show 0<d*z+r by nlinarith only [mul_pos dp b.halfPositive,normal.1])
    nlinarith only [wallU,formula,first,last,identity,positive,L,normal.1]
  · have formula : upper E (-R.s) R.c=q*A+k*H := by
      apply upper_pos_pos E (-R.s) R.c q k
      · rw [frame]; dsimp [c,s,d,q]; ring
      · rw [frame]; dsimp [c,s,d,k]; ring
      · exact qp.le
      · exact kp.le
    have first := mul_pos qp (show 0<A-(1-z) by linarith only [A0])
    have last := mul_pos kp (show 0<H+(13/50)*s by linarith only [H0])
    have f0 : 13/50<13/50+s*(1-z-(13/50)*c) := by
      have product := mul_pos h.sine
        (show 0<1-z-(13/50)*c by linarith only [b.halfUpper,b.cosineUpper])
      linarith only [product]
    have f1 : -(13/60)<c*(1-z)+(13/50)*s^2-1 := by
      have first := mul_pos (sub_pos.mpr b.cosine)
        (show 0<1-z by linarith only [b.halfUpper])
      have last := mul_pos (show 0<1/6-z by linarith only [b.halfUpper])
        (by norm_num : (0:ℝ)<47/50)
      nlinarith only [first,last,sq_nonneg s]
    have weighted0 := mul_pos dp (sub_pos.mpr f0)
    have weighted1 := mul_nonneg normal.1
      (show 0≤c*(1-z)+(13/50)*s^2-1+13/60 by linarith only [f1])
    have gap : 0<q*(1-z)-(13/50)*s*k-(r-(13/50)*d) := by
      dsimp [q,k] at *
      nlinarith only [weighted0,weighted1,normal.2.1,dp]
    nlinarith only [wallV,formula,first,last,gap,K]

private theorem southeast_positive_upper (E : OpenSquare) (h : Southeast E)
    (d r : ℝ) (dp : 0<d) (alpha : 0<E.c*d+E.s*r)
    (delta : 0≤E.c*r-E.s*d) :
    (E.c*d+E.s*r)*(1-half E.c E.s)<upper E d r := by
  let c := E.c
  let s := E.s
  let z := half c s
  let A := E.loU+E.side
  let H := E.loV+E.side
  let B := (E.side*(c+s)-1)/s
  let k := c*d+s*r
  let q := c*r-s*d
  have b := south_bounds c s h.cosine h.sine h.small E.unit_normal
  have relation : s*B=E.side*(c+s)-1 := by
    calc
      s*B=B*s := mul_comm _ _
      _=E.side*(c+s)-1 := div_mul_cancel₀ _ (ne_of_gt h.sine)
  have floor : s*B<s*A+c*H := by
    rw [relation]
    exact h.floor
  have nonpositive := mul_nonpos_of_nonneg_of_nonpos h.cosine.le h.upperV
  have lower : B<A := by
    have weighted : 0<s*(A-B) := by nlinarith only [floor,nonpositive]
    exact sub_pos.mp (pos_of_mul_pos_right weighted h.sine.le)
  have base : 1-z<B := by
    have product := mul_pos (sub_pos.mpr h.side) (add_pos h.cosine h.sine)
    have weighted : 0<s*(B-(1-z)) := by nlinarith only [relation,b.circle,product]
    exact sub_pos.mp (pos_of_mul_pos_right weighted h.sine.le)
  have formula : upper E d r=k*A+q*H := by
    exact upper_pos_pos E d r k q
      (by dsimp [c,s,k]; ring) (by dsimp [c,s,q]; ring) alpha.le delta
  have first := mul_pos dp (sub_pos.mpr lower)
  have last := mul_nonneg delta (sub_nonneg.mpr floor.le)
  have identity : c*(upper E d r-k*B)=d*(A-B)+q*(s*A+c*H-s*B) := by
    rw [formula]
    dsimp [c,s,k,q]
    linear_combination d*(A-B)*E.unit_normal
  have weighted : 0<c*(upper E d r-k*B) := by
    rw [identity]
    exact add_pos_of_pos_of_nonneg first last
  have strict := sub_pos.mp (pos_of_mul_pos_right weighted h.cosine.le)
  exact (mul_lt_mul_of_pos_left base alpha).trans strict

/-- A nonnegative right frame, with the coupled floor used before any
independent face relaxation. No upper bound on the common side is needed. -/
theorem southeast_positive_small (E R : OpenSquare)
    (h : Southeast E) (right : Right R) (same : E.side=R.side)
    (normal : Normal R.c R.s)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) : R.s<(2/5)*R.c := by
  let c := E.c
  let s := E.s
  let d := R.c
  let r := R.s
  let z := half c s
  let A := E.loU+E.side
  let H := E.loV+E.side
  let k := c*d+s*r
  let q := c*r-s*d
  have b := south_bounds c s h.cosine h.sine h.small E.unit_normal
  have rb := normal_bounds normal
  have dp : 0<d := by dsimp [d]; linarith only [rb.1]
  have faces := south_faces E h
  have A0 : 1-z<A := faces.2.2.2
  have Ap : 0<A := by linarith only [A0,b.halfUpper]
  have kp : 0<k := by
    have first := mul_pos h.cosine dp
    have last := mul_nonneg h.sine.le normal.1
    dsimp [k,c,s,d,r] at *
    nlinarith only [first,last]
  have L : R.loU<d-(13/50)*r := by
    have point := (right.bar (-13/50) (by norm_num) (by norm_num)).1
    dsimp [d,r]
    nlinarith only [point]
  have J : -r+(2/5)*d<R.loV+R.side := by
    have point := (right.bar (2/5) (by norm_num) (by norm_num)).2.2.2
    dsimp [d,r]
    nlinarith only [point]
  have axes := positive_axes E R same h.cosine h.sine.le dp normal.1
    (13/50) 0 h.forward (right.bar 0 (by norm_num) (by norm_num)) (by norm_num) apart
  apply lt_of_not_ge
  intro large
  have qp : 0<q := by
    have first := mul_pos
      (show 0<(2/5)*c-s by linarith only [h.small,h.sine]) dp
    have last := mul_nonneg h.cosine.le (sub_nonneg.mpr large)
    dsimp [q,c,s,d,r] at *
    nlinarith only [first,last]
  rcases axes with own|transverse|wallU|wallV
  · have formula : lower R c s=k*R.loU-q*(R.loV+R.side) := by
      have exactSupport := lower_pn R c s k (-q)
        (by dsimp [c,s,d,r,k]) (by dsimp [c,s,d,r,q]; ring)
        kp.le (by linarith only [qp])
      rw [exactSupport]
      ring
    have first := mul_lt_mul_of_pos_left L kp
    have last := mul_lt_mul_of_pos_left J qp
    have identity : k*(d-(13/50)*r)-q*(-r+(2/5)*d)=
        c-(33/50)*c*d*r+s*((2/5)*d^2-(13/50)*r^2) := by
      dsimp [k,q]
      linear_combination c*normal.2.2
    have loss := positive_loss c s z d r b normal large
    have eta : c-1+z=z*(1-s) := by nlinarith only [b.circle]
    change A≤lower R c s at own
    nlinarith only [own,A0,formula,first,last,identity,loss,b.eta,eta]
  · exact south_transverse_blocked E R h right transverse
  · have support := southeast_positive_upper E h d r dp kp qp.le
    let P := z*(c+s)
    let Q := 13/50+s*(1-z)
    have Qp : 0<Q := by
      have product := mul_pos h.sine (show 0<1-z by linarith only [b.halfUpper])
      dsimp [Q]; linarith only [product]
    have first := mul_pos dp (show 0<(2/5)*Q-P by
      dsimp [P,Q]; linarith only [b.key])
    have last := mul_nonneg (sub_nonneg.mpr large) Qp.le
    have gap : 0< -d*P+r*Q := by nlinarith only [first,last]
    have identity : k*(1-z)-d+(13/50)*r= -d*P+r*Q := by
      dsimp [k,P,Q]
      linear_combination d*b.circle
    nlinarith only [support,wallU,L,gap,identity]
  · have strong : 1/2<k := by
      have first := mul_pos (sub_pos.mpr b.cosine) dp
      have last := mul_nonneg h.sine.le normal.1
      dsimp [k]
      nlinarith only [first,last,rb.1]
    have formula : upper E r (-d)=q*A-k*E.loV := by
      have exactSupport := upper_pos_neg E r (-d) q (-k)
        (by dsimp [c,s,k,q]; ring) (by dsimp [c,s,k,q]; ring)
        qp.le (by linarith only [kp])
      rw [exactSupport]
      ring
    have first := mul_nonneg qp.le Ap.le
    have last := mul_nonneg kp.le
      (show 0≤-E.loV-E.side by linarith only [h.upperV])
    have sideR : 1<R.side := by simpa only [same] using h.side
    have bound := wall_lower R right dp.le r (-d) normal.1 (by linarith only [dp])
    have dot : r*R.c+(-d)*R.s=0 := by dsimp [r,d]; ring
    have cross : -r*R.s+(-d)*R.c= -1 := by
      dsimp [r,d]
      nlinarith only [R.unit_normal]
    rw [abs_of_nonneg normal.1,dot,cross] at bound
    norm_num only [abs_zero,abs_neg,abs_one,zero_add] at bound
    have coefficient : 0<1+r*(d+r) := by
      nlinarith only [mul_nonneg normal.1 (show 0≤d+r by linarith only [dp,normal.1])]
    have strict := mul_pos (sub_pos.mpr sideR) coefficient
    have order := mul_nonneg normal.1 (sub_nonneg.mpr normal.2.1)
    have lower : lower R r (-d)<1/2 := by
      nlinarith only [bound,strict,order,sq_nonneg (r-1)]
    have opposite : ABTransverse.lower R r (-d)=-(R.loV+R.side) := by
      simpa only [neg_neg,(ownV R).2] using lower_neg R (-R.s) R.c
    have sideStrict := mul_pos (sub_pos.mpr h.side) kp
    nlinarith only [wallV,opposite,lower,formula,first,last,strong,sideStrict]

end
#print axioms southeast_negative_small
#print axioms southeast_positive_small
end N12Compact.C1092TwoFifths
