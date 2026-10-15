import Compact.Geometry.PositiveCentralPositiveLeftBounds
import Compact.Geometry.CornerWallMarkerMixedBounds

/-! The other positive-left longitudinal support. Three continuous
relative-angle ranges are bounded at the bottom and central normals.
The interpolation is an exact unit-circle chord, with no angle grid. -/
namespace N12Compact.PositiveCentralPositiveLeftArc

open C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder

private theorem arc_between {p q C S l r b u v : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (left : q≤r) (right : r≤S) (up : 0≤u)
    (first : 0≤b+u*p+v*q) (last : 0≤b+u*C+v*S) :
    0≤b+u*l+v*r := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have lb := normal_bounds ln
  have pp : 0≤p := by linarith only [ob.1]
  have cp : 0≤C := by linarith only [ab.1]
  have lp : 0≤l := by linarith only [lb.1]
  by_cases same : S=q
  · have rs : r=q := by linarith only [left,right,same]
    have lc : l=p := by nlinarith only [ln.2.2,on.2.2,rs,ob.1,lb.1]
    simpa only [lc,rs] using first
  · have gap : 0<S-q := by linarith only [left,right,same]
    let T := (S-r)*p+(r-q)*C
    have tp : 0≤T := add_nonneg
      (mul_nonneg (sub_nonneg.mpr right) pp)
      (mul_nonneg (sub_nonneg.mpr left) cp)
    have product := mul_nonneg
      (mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right))
      (add_nonneg (sq_nonneg (p-C)) (sq_nonneg (S-q)))
    have identity : (S-q)^2*l^2-T^2=
        (r-q)*(S-r)*((p-C)^2+(S-q)^2) := by
      dsimp [T]
      linear_combination (S-q)^2*ln.2.2-
        (S-r)*(S-q)*on.2.2-(r-q)*(S-q)*an.2.2
    have chord : T≤(S-q)*l := by
      by_contra no
      have bad := mul_pos
        (show 0<T-(S-q)*l by linarith only [no])
        (show 0<T+(S-q)*l by
          have nonnegative := mul_nonneg gap.le lp
          linarith only [no,nonnegative])
      nlinarith only [bad,identity,product]
    have firstWeight := mul_nonneg (sub_nonneg.mpr right) first
    have lastWeight := mul_nonneg (sub_nonneg.mpr left) last
    have correction := mul_nonneg up (sub_nonneg.mpr chord)
    have scaled : 0≤(S-q)*(b+u*l+v*r) := by
      dsimp [T] at correction
      nlinarith only [firstWeight,lastWeight,correction]
    exact nonneg_of_mul_nonneg_right scaled gap

private theorem self_margin {p q : ℝ} (on : Normal p q) :
    0≤2-2*(p+q)+(q/p)*(B p q+1) := by
  have ob := normal_bounds on
  have pp : 0<p := by linarith only [ob.1]
  have pB : p*B p q=p-2*p*q+q*(1-q) := by
    dsimp [B]
    field_simp [ne_of_gt pp] <;> ring
  have identity :
      p^2*(2-2*(p+q)+(q/p)*(B p q+1))=(1-p)^2*(1-q) := by
    calc
      _ = 2*p^2-2*p^2*(p+q)+p*q*(B p q+1) := by
        field_simp [ne_of_gt pp] <;> ring
      _ = _ := by
        linear_combination q*pB+(1-2*p-q)*on.2.2
  have product := mul_nonneg (sq_nonneg (1-p))
    (sub_nonneg.mpr ob.2.2.2.1)
  have scaled : 0≤p^2*(2-2*(p+q)+(q/p)*(B p q+1)) := by
    nlinarith only [identity,product]
  exact nonneg_of_mul_nonneg_right scaled (sq_pos_of_pos pp)

private theorem zero_margin {p q C S : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S) :
    0≤1-C-S+(S/p)*(B p q+q) := by
  have ob := normal_bounds on
  have pp : 0<p := by linarith only [ob.1]
  have qp : 0<1+q := by linarith only [on.1]
  have identity : (B p q+q)/p=(1-q)/p+q/(1+q) := by
    calc
      _ = (1-q)/p+q*(1-q)/p^2 := by
        dsimp [B]; field_simp [ne_of_gt pp] <;> ring
      _ = _ := by
        have ratio : q*(1-q)/p^2=q/(1+q) := by
          apply (div_eq_div_iff (ne_of_gt (sq_pos_of_pos pp)) (ne_of_gt qp)).2
          linear_combination -q*on.2.2
        rw [ratio]
  have first : 1-q≤(1-q)/p := by
    apply (le_div_iff₀ pp).2
    have product := mul_nonneg (sub_nonneg.mpr ob.2.1)
      (sub_nonneg.mpr ob.2.2.2.1)
    nlinarith only [product]
  have second : q/2≤q/(1+q) := by
    apply (le_div_iff₀ qp).2
    have product := mul_nonneg on.1 (sub_nonneg.mpr ob.2.2.2.1)
    nlinarith only [product]
  have bound : 1-q/2≤(B p q+q)/p := by linarith only [identity,first,second]
  have weighted := mul_nonneg an.1 (sub_nonneg.mpr bound)
  have angle := mul_nonneg an.1 (sub_nonneg.mpr order)
  nlinarith only [weighted,angle,an.2.2,sq_nonneg (1-C)]

private theorem bottom_margin {p q C S : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S) :
    0≤1-2*(C+S)+(S/p)*B p q+p*(C+S)+(S*q/p)*(p+q) := by
  have ob := normal_bounds on
  have pp : 0<p := by linarith only [ob.1]
  let a := 2-p
  let b := 2-p-q-(q^2+B p q)/p
  have ap : 0≤a := by dsimp [a]; linarith only [ob.2.1]
  have coefficient : a*q-p*b=2*(1-p)+q*(1-q)/p := by
    calc
      _ = 2*(1-p)+q*(1-q)/p+(p^2+q^2-1) := by
        dsimp [a,b,B]
        field_simp [ne_of_gt pp] <;> ring
      _ = _ := by rw [on.2.2]; ring
  have coefficientPositive : 0≤a*q-p*b := by
    rw [coefficient]
    exact add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ob.2.1))
      (div_nonneg (mul_nonneg on.1 (sub_nonneg.mpr ob.2.2.2.1)) pp.le)
  have first := mul_nonneg ap (sub_nonneg.mpr (dot_le_one on an))
  have second := mul_nonneg coefficientPositive (sub_nonneg.mpr order)
  have identity : p*((1-a*C-b*S)-(1-a*p-b*q))=
      a*(1-(p*C+q*S))+(a*q-p*b)*(S-q) := by
    linear_combination a*on.2.2
  have monotone : 1-a*p-b*q≤1-a*C-b*S := by
    have scaled : 0≤p*((1-a*C-b*S)-(1-a*p-b*q)) := by
      nlinarith only [identity,first,second]
    have gap := nonneg_of_mul_nonneg_right scaled pp
    linarith only [gap]
  have form : 1-a*C-b*S=
      1-2*(C+S)+(S/p)*B p q+p*(C+S)+(S*q/p)*(p+q) := by
    dsimp [a,b]
    field_simp [ne_of_gt pp] <;> ring
  have selfForm : 1-a*p-b*q=2-2*(p+q)+(q/p)*(B p q+1) := by
    calc
      _ = 2-2*(p+q)+(q/p)*(B p q+1)+(1+q/p)*(p^2+q^2-1) := by
        dsimp [a,b]
        field_simp [ne_of_gt pp] <;> ring
      _ = _ := by rw [on.2.2]; ring
  have base := self_margin on
  linarith only [monotone,form,selfForm,base]

private theorem central_margin {p q C S : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S)
    (wide : 4/5≤C) (small : S≤3/5) :
    0≤2-2*(C+S)+C*S+(S/p)*(B p q+q*S) := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0<C := by linarith only [ab.1]
  have cosine := cosine_order an on order
  have cross : q*C≤S*p := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr order)
    have second := mul_nonneg an.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,second]
  have ratio : q/p≤S/C := (div_le_div_iff₀ pp cp).2 cross
  have ratioPositive : 0≤q/p := div_nonneg on.1 pp.le
  have ratioPositiveA : 0≤S/C := div_nonneg an.1 cp.le
  have squares := mul_nonneg (sub_nonneg.mpr ratio)
    (add_nonneg ratioPositiveA ratioPositive)
  have marker := CornerWallMarkerMixedBounds.g_order on an order small wide
  have bottomForm : CornerWallMarkerMixedBounds.G p q=
      (B p q+q)/p+(43/500)*(q/p)^2 := by
    dsimp [CornerWallMarkerMixedBounds.G,CornerWallMarkerMixedBounds.boundary,B]
    field_simp [ne_of_gt pp] <;> ring
  have centralForm : CornerWallMarkerMixedBounds.G C S=
      (B C S+S)/C+(43/500)*(S/C)^2 := by
    dsimp [CornerWallMarkerMixedBounds.G,CornerWallMarkerMixedBounds.boundary,B]
    field_simp [ne_of_gt cp] <;> ring
  have coarse : (B C S+S)/C≤(B p q+q)/p := by
    nlinarith only [marker,bottomForm,centralForm,squares]
  have change := mul_nonneg (sub_nonneg.mpr ab.2.2.2.1) (sub_nonneg.mpr ratio)
  have orderH : (B C S+S^2)/C≤(B p q+q*S)/p := by
    nlinarith only [coarse,change]
  have weighted := mul_nonneg an.1 (sub_nonneg.mpr orderH)
  have selfForm : C*S+(S/C)*(B C S+S^2)=(S/C)*(B C S+1) := by
    field_simp [ne_of_gt cp]
    <;> linear_combination S*an.2.2
  have base := self_margin an
  nlinarith only [weighted,selfForm,base]

/-- Full positive-left support coefficient after eliminating its actual
left wall. All relative left angles are covered continuously. -/
theorem central_axis_margin {p q C S l r : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (order : q≤S) (wide : 4/5≤C) (small : S≤3/5) :
    p*(2*(C+S)-1)≤S*B p q+
      ((p*C+q*S)*(l+r)+p*(C*l+S*r+|S*l-C*r|)+
        S*(|p*r-q*l|+p*l+q*r))/2 := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0≤C := by linarith only [ab.1]
  have lp : 0≤l := by linarith only [lb.1]
  have qn : 0≤q := on.1
  have sn : 0≤S := an.1
  have rn : 0≤r := ln.1
  let b := 1-2*(C+S)+(S/p)*B p q
  have zero := zero_margin on an order
  have bottom := bottom_margin on an order
  have central := central_margin on an order wide small
  by_cases low : r≤q
  · have lc := cosine_order on ln low
    have cl := cosine_order an ln (le_trans low order)
    have d : p*r-q*l≤0 := by
      have first := mul_nonneg pp.le (sub_nonneg.mpr low)
      have second := mul_nonneg on.1 (sub_nonneg.mpr lc)
      nlinarith only [first,second]
    have h : 0≤S*l-C*r := by
      have first := mul_nonneg cp (sub_nonneg.mpr (le_trans low order))
      have second := mul_nonneg an.1 (sub_nonneg.mpr cl)
      nlinarith only [first,second]
    have coeff : 0≤C+S+S*q/p := by positivity
    have arc := CornerWallCycleBounds.arc_nonnegative on ln low coeff
      (show 0≤b+(C+S+S*q/p) by dsimp [b]; nlinarith only [zero])
      (show 0≤b+(C+S+S*q/p)*p+(S*q/p)*q by dsimp [b]; nlinarith only [bottom])
    rw [abs_of_nonneg h,abs_of_nonpos d]
    have scaled := mul_nonneg pp.le arc
    have form : p*(b+(C+S+S*q/p)*l+(S*q/p)*r)=S*B p q+
        ((p*C+q*S)*(l+r)+p*(C*l+S*r+(S*l-C*r))+
          S*(-(p*r-q*l)+p*l+q*r))/2-p*(2*(C+S)-1) := by
      dsimp [b]
      field_simp [ne_of_gt pp] <;> ring
    nlinarith only [scaled,form]
  · have qr : q≤r := le_of_lt (lt_of_not_ge low)
    have lc := cosine_order ln on qr
    have d : 0≤p*r-q*l := by
      have first := mul_nonneg lp (sub_nonneg.mpr qr)
      have second := mul_nonneg ln.1 (sub_nonneg.mpr lc)
      nlinarith only [first,second]
    by_cases middle : r≤S
    · have cl := cosine_order an ln middle
      have h : 0≤S*l-C*r := by
        have first := mul_nonneg cp (sub_nonneg.mpr middle)
        have second := mul_nonneg an.1 (sub_nonneg.mpr cl)
        nlinarith only [first,second]
      have arc := arc_between on an ln qr middle (show 0≤C+S by positivity)
        (show 0≤b+(C+S)*p+(S*(1+q/p))*q by dsimp [b]; nlinarith only [bottom])
        (show 0≤b+(C+S)*C+(S*(1+q/p))*S by
          dsimp [b]; nlinarith only [central,an.2.2])
      rw [abs_of_nonneg h,abs_of_nonneg d]
      have scaled := mul_nonneg pp.le arc
      have form : p*(b+(C+S)*l+(S*(1+q/p))*r)=S*B p q+
          ((p*C+q*S)*(l+r)+p*(C*l+S*r+(S*l-C*r))+
            S*((p*r-q*l)+p*l+q*r))/2-p*(2*(C+S)-1) := by
        dsimp [b]
        field_simp [ne_of_gt pp] <;> ring
      nlinarith only [scaled,form]
    · have sr : S≤r := le_of_lt (lt_of_not_ge middle)
      have cl := cosine_order ln an sr
      have h : S*l-C*r≤0 := by
        have first := mul_nonneg lp (sub_nonneg.mpr sr)
        have second := mul_nonneg ln.1 (sub_nonneg.mpr cl)
        nlinarith only [first,second]
      have slope : C*r≤(C+S+S*q/p)*l := by
        have first := mul_nonneg cp (sub_nonneg.mpr ln.2.1)
        have second : 0≤(S+S*q/p)*l := by positivity
        nlinarith only [first,second]
      have monotone := linear_arc_max ln an sr cp slope
      have arc : 0≤b+C*l+(C+S+S*q/p)*r := by
        dsimp [b]
        nlinarith only [monotone,central,an.2.2]
      rw [abs_of_nonpos h,abs_of_nonneg d]
      have scaled := mul_nonneg pp.le arc
      have form : p*(b+C*l+(C+S+S*q/p)*r)=S*B p q+
          ((p*C+q*S)*(l+r)+p*(C*l+S*r-(S*l-C*r))+
            S*((p*r-q*l)+p*l+q*r))/2-p*(2*(C+S)-1) := by
        dsimp [b]
        field_simp [ne_of_gt pp] <;> ring
      nlinarith only [scaled,form]

#print axioms central_axis_margin
end N12Compact.PositiveCentralPositiveLeftArc
