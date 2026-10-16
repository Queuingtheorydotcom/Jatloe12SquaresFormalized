import Compact.Geometry.PositiveCentralCrossMargin
import Compact.Geometry.PositiveCentralPositiveLeftBounds
import Compact.Geometry.PositiveLeftOwnVEndpoint

/-! The vertex margin for an incoming separator on the left square's
own V face. The central angle is removed monotonically; this file proves
the bottom-angle endpoint by an exact circle-chord identity. -/
namespace N12Compact.PositiveLeftOwnVBounds

open C977CornerCubic C977CornerSectorBounds PositiveCentralCrossMargin
open PositiveCentralPositiveLeftBounds
set_option Elab.async false

/-- At the bottom-angle endpoint the entire smaller left-angle arc is
above its two endpoints. Its remainder is an explicit nonnegative chord
correction, so no angular enumeration is used. -/
theorem endpoint_bottom {p q l r : ℝ}
    (on : Normal p q) (ln : Normal l r) (shallow : 9/10≤p) (order : r≤q) :
    l^2*(1-vertexDefect p q-q*(1-p))+l*r*(2-q*(1-p))≤
      l+r*F p q l r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [shallow]
  have lp : 0<l := by linarith only [lb.1]
  have cosine : p≤l := cosine_order on ln order
  have qp : 0≤q := on.1
  have rp : 0≤r := ln.1
  have qsmall : q≤11/25 := by
    have square := mul_nonneg (sub_nonneg.mpr shallow)
      (show 0≤p+9/10 by linarith only [shallow])
    by_contra no
    have bad := mul_pos (show 0<q-11/25 by linarith only [no])
      (show 0<q+11/25 by linarith only [qp])
    nlinarith only [bad,square,on.2.2]
  let X := 1-vertexDefect p q-q*(1-p)
  let Y := 2-q*(1-p)
  let a := 2-p-2*q+p*q
  let E := -2+q*(p+q-457/500)/p+X
  let D (c s : ℝ) := c+s-a*c*s+E*s^2-X
  have Xupper : X≤1 := by
    have first : 0≤vertexDefect p q := by
      dsimp [vertexDefect]
      exact div_nonneg
        (mul_nonneg (sub_nonneg.mpr ob.2.1)
          (sub_nonneg.mpr ob.2.2.2.1)) pp.le
    have second := mul_nonneg qp (sub_nonneg.mpr ob.2.1)
    dsimp [X]
    linarith only [first,second]
  have ap : 0≤a := by
    have product := mul_nonneg pp.le qp
    dsimp [a]
    nlinarith only [product,ob.2.1,qsmall]
  have au : a≤1 := by
    have product := mul_nonneg qp (sub_nonneg.mpr ob.2.1)
    dsimp [a]
    nlinarith only [product,ob.2.2.2.2.1]
  have eupper : E≤-(7/10) := by
    have bracket : p+q-457/500≤263/500 := by
      linarith only [ob.2.1,qsmall]
    have first := mul_nonneg qp (sub_nonneg.mpr bracket)
    have numerator : q*(p+q-457/500)≤(3/10)*p := by
      nlinarith only [first,qsmall,shallow]
    have fraction : q*(p+q-457/500)/p≤3/10 :=
      (div_le_iff₀ pp).mpr numerator
    dsimp [E]
    linarith only [fraction,Xupper]
  have active : max (q*l-p*r) 0=q*l-p*r := by
    have first := mul_nonneg lp.le (sub_nonneg.mpr order)
    have second := mul_nonneg rp (sub_nonneg.mpr cosine)
    apply max_eq_left
    nlinarith only [first,second]
  have gap_identity :
      l+r*F p q l r-l^2*X-l*r*Y=D l r := by
    have scaled : p*((l+r*F p q l r-l^2*X-l*r*Y)-D l r)=0 := by
      dsimp [D,E,a,Y,F]
      rw [active]
      field_simp [pp.ne']
      <;> linear_combination 500*((-r^2)*on.2.2-p*X*ln.2.2)
    have difference := (mul_eq_zero.mp scaled).resolve_left pp.ne'
    linarith only [difference]
  have diagonal : F p q p q=2-2*q+q*(1-(457/500)*q)/p := by
    dsimp [F]
    rw [show q*p-p*q=0 by ring, max_self]
    field_simp [pp.ne']
    <;> linear_combination (500*p)*on.2.2
  have endpoint_formula :
      p*(p+q*F p q p q-p^2*X-p*q*Y)=
        2*p^2-2*p^3+q*(2*p-3*p^2+2*p^3-p^4)+
          q^2*(1-2*p+p^2-p^3)-(457/500)*q^3 := by
    rw [diagonal]
    dsimp [X,Y,vertexDefect]
    field_simp [pp.ne'] <;> ring
  have endpoint_identity :
      (1+p)*p*(p+q*F p q p q-p^2*X-p*q*Y)=
        q^2*(p^2*q*(p+q-1)+q*((543/500)*p-457/500)+1-p) := by
    rw [show (1+p)*p*(p+q*F p q p q-p^2*X-p*q*Y)=
      (1+p)*(p*(p+q*F p q p q-p^2*X-p*q*Y)) by ring]
    rw [endpoint_formula]
    linear_combination
      (-p^2*q^2+(-p^3+p^2-2*p)*q-2*p^2)*on.2.2
  have endpoint_nonnegative : 0≤p+q*F p q p q-p^2*X-p*q*Y := by
    have first := mul_nonneg (mul_nonneg (sq_nonneg p) qp)
      (show 0≤p+q-1 by linarith only [ob.2.2.2.2.1])
    have second := mul_nonneg qp
      (show 0≤(543/500)*p-457/500 by linarith only [shallow])
    have right := mul_nonneg (sq_nonneg q)
      (show 0≤p^2*q*(p+q-1)+q*((543/500)*p-457/500)+1-p by
        linarith only [first,second,ob.2.1])
    rw [←endpoint_identity] at right
    exact nonneg_of_mul_nonneg_right right
      (mul_pos (by linarith only [pp] : 0<1+p) pp)
  have endpoint_gap : p+q*F p q p q-p^2*X-p*q*Y=D p q := by
    have scaled : p*((p+q*F p q p q-p^2*X-p*q*Y)-D p q)=0 := by
      rw [diagonal]
      dsimp [D,E,a,Y]
      field_simp [pp.ne']
      <;> linear_combination (500*(-q^2-p*q-p*X))*on.2.2
    have difference := (mul_eq_zero.mp scaled).resolve_left pp.ne'
    linarith only [difference]
  have endpoint : 0≤D p q := by
    rw [←endpoint_gap]
    exact endpoint_nonnegative
  have axis : 0≤D 1 0 := by dsimp [D]; linarith only [Xupper]
  have chord := arc_chord on ln order (show (0:ℝ)≤0 by norm_num)
  have circle_chord : 0≤q*l-q+r-r*p := by
    have identity :
        q*((1-(0:ℝ)*r)*(p*l+q*r))-((q-r)*p+r*(1-0*q))=
          p*(q*l-q+r-r*p) := by
      linear_combination r*on.2.2
    have scaled : 0≤p*(q*l-q+r-r*p) := by
      linarith only [chord,identity]
    exact nonneg_of_mul_nonneg_right scaled pp
  have radial : p*(l-p)≤q*(q-r) := by
    nlinarith only [dot_le_one on ln,on.2.2]
  have coefficient : a*q≤p/2 := by
    have product := mul_nonneg qp (sub_nonneg.mpr au)
    nlinarith only [product,qsmall,shallow]
  have nonnegative := mul_nonneg ap qp
  have radial_weight := mul_nonneg (mul_nonneg nonnegative rp)
    (sub_nonneg.mpr radial)
  have coefficient_weight := mul_nonneg
    (mul_nonneg qp rp) (sub_nonneg.mpr order)
  have correction : 0≤ -a*q*r*(l-p)-E*q*r*(q-r) := by
    have first := mul_nonneg coefficient_weight
      (show 0≤-(p*E)-a*q by
        have e := mul_nonneg pp.le (sub_nonneg.mpr eupper)
        nlinarith only [e,coefficient,pp])
    have scaled : 0≤p*(-a*q*r*(l-p)-E*q*r*(q-r)) := by
      nlinarith only [radial_weight,first]
    exact nonneg_of_mul_nonneg_right scaled pp
  have identity : q*D l r-(q-r)*D 1 0-r*D p q=
      (q*l-q+r-r*p)-a*q*r*(l-p)-E*q*r*(q-r) := by
    dsimp [D]
    ring
  have first := mul_nonneg (sub_nonneg.mpr order) axis
  have second := mul_nonneg rp endpoint
  have scaled : 0≤q*D l r := by
    nlinarith only [identity,circle_chord,correction,first,second]
  have result : 0≤D l r := by
    by_cases zero : q=0
    · have rzero : r=0 := by linarith only [rp,order,zero]
      have lone : l=1 := by nlinarith only [ln.2.2,rzero,lp]
      simpa only [rzero,lone] using axis
    · exact nonneg_of_mul_nonneg_right scaled
        (lt_of_le_of_ne qp (Ne.symm zero))
  change l^2*X+l*r*Y≤l+r*F p q l r
  linarith only [gap_identity,result]

/-- The central upper-left vertex is bounded by the larger of the
bottom and left angles. This comparison uses the genuine vertex defect,
and removes the central angle without replacing the square by a point. -/
theorem vertex_margin {p q C S l r : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (order : q≤S) (relative : r≤S)
    (shallow : 9/10≤p) (wide : 4/5≤C) (small : S≤3/5) :
    l^2*(1-vertexDefect C S-S*(1-p))+l*r*(2-S*(1-C))≤
      l+r*F p q l r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have lp : 0≤l := by linarith only [lb.1]
  have lr : 0≤l*r := mul_nonneg lp ln.1
  rcases le_total q r with leftHigher | bottomHigher
  · have endpoint := PositiveLeftOwnVEndpoint.endpoint_left on ln shallow leftHigher
    have cosine := cosine_order an ln relative
    have defect := defect_order ln an relative wide small
    have first := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr defect)
    have second := mul_nonneg (sq_nonneg l)
      (mul_nonneg (sub_nonneg.mpr relative) (sub_nonneg.mpr ob.2.1))
    have third := mul_nonneg lr
      (mul_nonneg (sub_nonneg.mpr relative) (sub_nonneg.mpr lb.2.1))
    have fourth := mul_nonneg (mul_nonneg lr an.1) (sub_nonneg.mpr cosine)
    nlinarith only [endpoint,first,second,third,fourth]
  · have endpoint := endpoint_bottom on ln shallow bottomHigher
    have cosine := cosine_order an on order
    have defect := defect_order on an order wide small
    have first := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr defect)
    have second := mul_nonneg (sq_nonneg l)
      (mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr ob.2.1))
    have third := mul_nonneg lr
      (mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr ob.2.1))
    have fourth := mul_nonneg (mul_nonneg lr an.1) (sub_nonneg.mpr cosine)
    nlinarith only [endpoint,first,second,third,fourth]

#print axioms endpoint_bottom
#print axioms vertex_margin
end N12Compact.PositiveLeftOwnVBounds
