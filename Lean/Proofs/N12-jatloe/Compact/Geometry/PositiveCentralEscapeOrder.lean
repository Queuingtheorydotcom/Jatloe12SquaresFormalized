import Compact.Geometry.PositiveCentralPositiveBottom
import Compact.Geometry.NegativeWallTopSeed
import Compact.Geometry.CornerOuterOrderEndpoint
import Compact.Geometry.CornerOuterOrderMonotone
import Compact.Geometry.FourSquareBLBridge

/-! Continuous support comparisons for the missing-(1,2) branch.
This file keeps the original northwest-marker restriction; dropping it
would invalidate the central-axis endpoint comparison. Its final theorem
also retains W's exclusion of (1,2.88), which is not currently an original
C696/C977 consequence: the adjacent upper corner is paired. -/
namespace N12Compact.PositiveCentralEscapeOrder

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner C977CornerSectorBounds

noncomputable def B (p q : ℝ) : ℝ := 1-2*q+q*(1-q)/p

private theorem B_alt {p q : ℝ} (normal : Normal p q) :
    B p q=1-2*q+p*q/(1+q) := by
  have b := normal_bounds normal
  have pp : p≠0 := ne_of_gt (by linarith only [b.1])
  have qp : 1+q≠0 := ne_of_gt (by linarith only [normal.1])
  have ratio : q*(1-q)/p=p*q/(1+q) := by
    apply (div_eq_div_iff pp qp).mpr
    linear_combination -q*normal.2.2
  unfold B
  rw [ratio]

private theorem half_order {p q C S : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S) :
    p*(1-S)≤C*(1-q) := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0<C := by linarith only [ab.1]
  have first := mul_nonneg (sub_nonneg.mpr order)
    (add_nonneg
      (mul_nonneg (show 0≤1-S by linarith only [ab.2.2.2.1])
        (show 0≤1-q by linarith only [ob.2.2.2.1]))
      (mul_nonneg pp.le cp.le))
  have identity :
      (p+C)*(C*(1-q)-p*(1-S)) =
        (S-q)*((1-S)*(1-q)+p*C) := by
    linear_combination (1-q)*an.2.2-(1-S)*on.2.2
  have scaled : 0≤(p+C)*(C*(1-q)-p*(1-S)) := by
    linarith only [first,identity]
  have gap := nonneg_of_mul_nonneg_right scaled
    (show 0<p+C by linarith only [pp,cp])
  linarith only [gap]

/-- The surviving positive-bottom support has a common lower bound
independent of its angle, as long as its tilt is below the central tilt. -/
theorem strong_base_bound {p q C S v : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S)
    (support : B p q < (p*S-q*C)*(2*(C+S)-1)+(p*C+q*S)*(v-1)) :
    1+(C+S)*(1-2*S)+C*(1-p)<C*v := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0<C := by linarith only [ab.1]
  have ratio := half_order on an order
  have ratioWeight := mul_nonneg on.1 (sub_nonneg.mpr ratio)
  have cosineWeight := mul_nonneg cp.le
    (mul_nonneg pp.le (sub_nonneg.mpr ob.2.1))
  have pB : p*B p q=p-2*p*q+q*(1-q) := by
    unfold B
    field_simp [pp.ne']
  have identity :
      p*C*((p*C+q*S)*(v-1)+(p*S-q*C)*(2*(C+S)-1)-B p q) =
      p*(p*C+q*S)*(C*v-(1+(C+S)*(1-2*S)))-
        p*C*(1-p)-q*(C*(1-q)-p*(1-S)) := by
    linear_combination -C*pB+(-p*q*(2*(C+S)-1))*an.2.2
  have kp : 0<p*C+q*S := by
    have first := mul_pos pp cp
    have second := mul_nonneg on.1 an.1
    linarith only [first,second]
  have strict := mul_pos (mul_pos pp cp) (sub_pos.mpr support)
  have scaled : p*C*(1-p)<p*(p*C+q*S)*(C*v-(1+(C+S)*(1-2*S))) := by
    nlinarith only [identity,strict,ratioWeight,cosineWeight]
  have positive : 0<C*v-(1+(C+S)*(1-2*S)) := by
    have product : 0<p*(p*C+q*S)*(C*v-(1+(C+S)*(1-2*S))) := by
      nlinarith only [scaled,cosineWeight]
    exact pos_of_mul_pos_right product (mul_nonneg pp.le kp.le)
  have dot : p*C+q*S≤1 := by
    nlinarith only [on.2.2,an.2.2,sq_nonneg (p-C),sq_nonneg (q-S)]
  have replacement := mul_nonneg (mul_nonneg pp.le (sub_nonneg.mpr dot)) positive.le
  have gap : 0<p*(C*v-(1+(C+S)*(1-2*S))-C*(1-p)) := by
    nlinarith only [scaled,replacement]
  have unscaled := pos_of_mul_pos_right gap pp.le
  linarith only [unscaled]

theorem base_bound {p q C S v : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S)
    (support : B p q < (p*S-q*C)*(2*(C+S)-1)+(p*C+q*S)*(v-1)) :
    1+(C+S)*(1-2*S)<C*v := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have defect := mul_nonneg
    (show 0≤C by linarith only [ab.1]) (sub_nonneg.mpr ob.2.1)
  have gap := strong_base_bound on an order support
  linarith only [gap,defect]

/-- The actual northwest-marker face cap gives enough central cosine
for the strict foreign-top-seed endpoint. -/
theorem northwest_threshold {C S v : ℝ} (normal : Normal C S)
    (floor : 1+(C+S)*(1-2*S)<C*v)
    (cap : v≤(47/20)*C-(33/20)*S) :
    81/100<C ∧ C*(47/25*C-S)≤1+(C+S)*(1-2*S) := by
  have b := normal_bounds normal
  have cp : 0<C := by linarith only [b.1]
  have weighted := mul_nonneg cp.le (sub_nonneg.mpr cap)
  have gap : 0<1+(7/20)*C*(C+S)-(C+S) := by
    nlinarith only [floor,weighted,normal.2.2]
  have cosine : 81/100<C := by
    by_contra no
    have upper : C≤81/100 := le_of_not_gt no
    have csq := mul_nonneg (sub_nonneg.mpr upper)
      (show 0≤81/100+C by linarith only [cp])
    have sine : 293/500≤S := by
      by_contra noS
      have small := mul_nonneg normal.1
        (show 0≤293/500-S by linarith only [noS])
      nlinarith only [csq,small,noS,normal.2.2]
    have difference := mul_nonneg (sub_nonneg.mpr normal.2.1)
      (show 0≤28/125-(C-S) by linarith only [upper,sine])
    have sum : 349/250≤C+S := by
      by_contra noSum
      have small := mul_nonneg (show 0≤C+S by linarith only [cp,normal.1])
        (show 0≤349/250-(C+S) by linarith only [noSum])
      nlinarith only [small,difference,noSum,normal.2.2]
    have lowerWeight := mul_nonneg (sub_nonneg.mpr sum)
      (show 0≤1-(7/20)*C by linarith only [b.2.1])
    nlinarith only [gap,lowerWeight,upper]
  have line : 22/25<C+(3/25)*S := by
    by_contra no
    have assumed : C+(3/25)*S≤22/25 := le_of_not_gt no
    have upper : C≤22/25 := by linarith only [assumed,normal.1]
    have arc := mul_nonneg (show 0≤C-81/100 by linarith only [cosine])
      (sub_nonneg.mpr upper)
    have product := mul_nonneg
      (show 0≤22-25*C-3*S by linarith only [assumed])
      (show 0≤22-25*C+3*S by linarith only [assumed,normal.1])
    nlinarith only [arc,product,normal.2.2,cosine]
  have sign := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤1-S by linarith only [b.2.2.2.1])
    (show 22/25-C-(3/25)*S≤0 by linarith only [line])
  constructor
  · exact cosine
  · nlinarith only [sign,normal.2.2]

/-- Decreasing the bottom angle to the wall angle only weakens the
required central upper-V face. This uses the exact continuous coefficient
differences, not a finite angle subdivision. -/
theorem lower_transfer {p q d t C S v : ℝ}
    (on : Normal p q) (wn : Normal d t) (an : Normal C S)
    (outer : t≤q) (inner : q≤S)
    (support : B p q < (p*S-q*C)*(2*(C+S)-1)+(p*C+q*S)*(v-1)) :
    B d t < (d*S-t*C)*(2*(C+S)-1)+(d*C+t*S)*(v-1) := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have ab := normal_bounds an
  have pp : 0<p := by linarith only [ob.1]
  have dp : 0<d := by linarith only [wb.1]
  have cp : 0<C := by linarith only [ab.1]
  have qp : 0<1+q := by linarith only [on.1]
  have tp : 0<1+t := by linarith only [wn.1]
  let r := CornerOuterOrderMonotone.cross p q d t
  let den := CornerOuterOrderMonotone.denominator q t
  let F := CornerOuterOrderMonotone.F p q d t
  let G := CornerOuterOrderMonotone.G p q d t
  let K := p*C+q*S
  let K0 := d*C+t*S
  let D := p*S-q*C
  let D0 := d*S-t*C
  let U := 2*(C+S)-1
  have kpos : 0<K := by
    have first := mul_pos pp cp
    have second := mul_nonneg on.1 an.1
    dsimp [K]
    linarith only [first,second]
  have k0pos : 0<K0 := by
    have first := mul_pos dp cp
    have second := mul_nonneg wn.1 an.1
    dsimp [K0]
    linarith only [first,second]
  have denpos : 0<den := mul_pos qp tp
  have cosine := cosine_order on wn outer
  have fpos : 0≤F := by
    have first := mul_nonneg denpos.le (sub_nonneg.mpr cosine)
    have second := mul_nonneg (mul_nonneg pp.le dp.le) (sub_nonneg.mpr outer)
    dsimp [F,CornerOuterOrderMonotone.F]
    nlinarith only [first,second]
  have differences := CornerOuterOrderMonotone.differences on wn outer
  change 0≤G-F ∧ 0≤p*F+q*G-den*r at differences
  have sum : p+q≤C+S := by
    have product := mul_nonneg (sub_nonneg.mpr inner)
      (show 0≤p+C-S-q by linarith only [on.2.1,an.2.1])
    have identity : (p+C)*(C+S-p-q)=(S-q)*(p+C-S-q) := by
      linear_combination an.2.2-on.2.2
    have scaled : 0≤(p+C)*(C+S-p-q) := by linarith only [identity,product]
    have gap := nonneg_of_mul_nonneg_right scaled
      (show 0<p+C by linarith only [pp,cp])
    linarith only [gap]
  have first := mul_nonneg fpos (sub_nonneg.mpr sum)
  have second := mul_nonneg differences.1 (sub_nonneg.mpr inner)
  have coefficient : 0≤F*C+G*S-den*r := by
    nlinarith only [first,second,differences.2]
  have fIdentity : den*(d*B p q-p*B d t+2*r)=F := by
    rw [B_alt on,B_alt wn]
    dsimp [den,r,F,CornerOuterOrderMonotone.denominator,
      CornerOuterOrderMonotone.cross,CornerOuterOrderMonotone.F]
    field_simp [qp.ne',tp.ne']
    ring
  have gIdentity : den*(t*B p q-q*B d t+2*r)=G := by
    rw [B_alt on,B_alt wn]
    dsimp [den,r,G,CornerOuterOrderMonotone.denominator,
      CornerOuterOrderMonotone.cross,CornerOuterOrderMonotone.G]
    field_simp [qp.ne',tp.ne']
    ring
  have crossIdentity : D0*K-D*K0=r := by
    dsimp [D0,K,D,K0,r,CornerOuterOrderMonotone.cross]
    linear_combination (d*q-p*t)*an.2.2
  have identity : den*(K0*B p q-K*B d t+U*r)=F*C+G*S-den*r := by
    dsimp [K0,K,U]
    linear_combination C*fIdentity+S*gIdentity
  have nonnegative : 0≤K0*B p q-K*B d t+U*r := by
    have scaled : 0≤den*(K0*B p q-K*B d t+U*r) := by
      linarith only [identity,coefficient]
    exact nonneg_of_mul_nonneg_right scaled denpos
  by_contra no
  have assumed : D0*U+K0*(v-1)≤B d t := le_of_not_gt no
  have high := mul_lt_mul_of_pos_left support k0pos
  change K0*B p q<K0*(D*U+K*(v-1)) at high
  have low := mul_le_mul_of_nonneg_left assumed kpos.le
  have scaledCross := congrArg (fun x : ℝ => U*x) crossIdentity
  clear_value r den F G K K0 D D0 U
  nlinarith only [high,low,scaledCross,nonnegative]

/-- At equal bottom and wall angles both genuine wall support modes are
impossible. The northwest cap is used only by the central-axis mode. -/
theorem endpoint_obstruction {d t C S v : ℝ}
    (wn : Normal d t) (an : Normal C S) (order : t≤S)
    (support : B d t < (d*S-t*C)*(2*(C+S)-1)+(d*C+t*S)*(v-1))
    (northwest : v≤(47/20)*C-(33/20)*S)
    (modes : d*v≤C*(t+(72/25)*d)-(C+S*d^2+C*d*t) ∨
      d+t-t^2-(72/25)*d*t <
        d*((C*d-S*t)*(2*(C+S)-1)-(S*d+C*t)*v)) : False := by
  have wb := normal_bounds wn
  have ab := normal_bounds an
  have dp : 0<d := by linarith only [wb.1]
  have cp : 0<C := by linarith only [ab.1]
  let K := d*C+t*S
  let D := d*S-t*C
  let k := C*d-S*t
  let h := S*d+C*t
  let J := d^2-t^2
  let U := 2*(C+S)-1
  let R := 2*J-(d+t)*B d t
  have kp : 0<K := by
    have first := mul_pos dp cp
    have second := mul_nonneg wn.1 an.1
    dsimp [K]
    linarith only [first,second]
  have kmax : K≤1 := by
    dsimp [K]
    nlinarith only [wn.2.2,an.2.2,sq_nonneg (d-C),sq_nonneg (t-S)]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dp.le) (mul_nonneg cp.le wn.1)
  rcases modes with central | wall
  · have lower := strong_base_bound wn an order support
    have plain := base_bound wn an order support
    have endpoint := (northwest_threshold an plain northwest).2
    have first := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (mul_nonneg cp.le (show 0≤1-t by linarith only [wb.2.2.2.1]))
    have second := mul_nonneg (sub_nonneg.mpr wb.2.1)
      (mul_nonneg dp.le (show 0≤1-S by linarith only [ab.2.2.2.1]))
    have upper : d*v≤d*((47/25)*C-S+1-d) := by
      nlinarith only [central,first,second]
    have upperScaled := mul_le_mul_of_nonneg_left upper cp.le
    have endpointScaled := mul_le_mul_of_nonneg_left endpoint dp.le
    have lowerScaled := mul_lt_mul_of_pos_left lower dp
    nlinarith only [upperScaled,endpointScaled,lowerScaled]
  · have relative : K*k+h*D=J := by
      dsimp [K,k,h,D,J]
      linear_combination (d^2-t^2)*an.2.2
    have product : h*K=d*t+C*S := by
      dsimp [h,K]
      linear_combination d*t*an.2.2+C*S*wn.2.2
    have sum : h+K=(d+t)*(C+S) := by dsimp [h,K]; ring
    have sums : d+t≤C+S := by
      have factor := mul_nonneg (sub_nonneg.mpr order)
        (show 0≤d+C-S-t by linarith only [wn.2.1,an.2.1])
      have identity : (d+C)*(C+S-d-t)=(S-t)*(d+C-S-t) := by
        linear_combination an.2.2-wn.2.2
      have scaled : 0≤(d+C)*(C+S-d-t) := by linarith only [factor,identity]
      have gap := nonneg_of_mul_nonneg_right scaled
        (show 0<d+C by linarith only [dp,cp])
      linarith only [gap]
    have quotient : 0≤t*(1-t)/d := div_nonneg
      (mul_nonneg wn.1 (show 0≤1-t by linarith only [wb.2.2.2.1])) dp.le
    have base : 2*(d-t)≤B d t+1 := by
      dsimp [B]
      linarith only [quotient,wb.2.1]
    have rmax : R≤d+t := by
      have scaled := mul_nonneg
        (show 0≤d+t by linarith only [dp,wn.1]) (sub_nonneg.mpr base)
      dsimp [R,J]
      nlinarith only [scaled]
    have chord := mul_nonneg (sub_nonneg.mpr sums)
      (show 0≤(C+S+d+t)/2-R by clear_value R; linarith only [sums,rmax])
    have radial : R*(C+S)-(C*S)≤R*(d+t)-d*t := by
      clear_value R
      nlinarith only [chord,an.2.2,wn.2.2]
    have tilt := mul_nonneg wn.1
      (show 0≤1-(22/25)*K by clear_value K; linarith only [kmax])
    have endpoint := CornerOuterOrderEndpoint.endpoint wn
    change R*(d+t)+t-J-2*d*t≤0 at endpoint
    have scalar : R*(C+S)+(22/25)*t*K-J-d*t-C*S≤0 := by
      clear_value R K J
      nlinarith only [radial,tilt,endpoint]
    have dB : d*B d t=d-2*d*t+t-t^2 := by
      dsimp [B]
      field_simp [dp.ne']
      ring
    have identity :
        d*(J*U-h*(B d t+K))-K*(d+t-t^2-(72/25)*d*t)=
          d*(R*(C+S)+(22/25)*t*K-J-d*t-C*S) := by
      have sumB := congrArg (fun x : ℝ => B d t*x) sum
      dsimp [U,R]
      linear_combination -d*product-d*sumB+K*dB
    have scalarScaled := mul_nonpos_of_nonneg_of_nonpos dp.le scalar
    have bound : d*(J*U-h*(B d t+K))≤K*(d+t-t^2-(72/25)*d*t) := by
      nlinarith only [identity,scalarScaled]
    have sWeight := mul_nonneg (mul_nonneg dp.le hp)
      (sub_nonneg.mpr support.le)
    have wWeight := mul_lt_mul_of_pos_left wall kp
    change K*(d+t-t^2-(72/25)*d*t)<K*(d*(k*U-h*v)) at wWeight
    have relativeScaled := congrArg (fun x : ℝ => d*U*x) relative
    change B d t<D*U+K*(v-1) at support
    change 0≤d*h*(D*U+K*(v-1)-B d t) at sWeight
    clear_value K D k h J U R
    nlinarith only [bound,sWeight,wWeight,relativeScaled]

/-- The actual support system forces the bottom tilt below the negative
wall tilt. Central ownership of (1,2) is not assumed. -/
theorem support_order (O A W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (an : Normal A.c A.s) (wn : Normal W.c t)
    (ws : W.s=-t) (sameOA : O.side=A.side) (sameAW : A.side=W.side)
    (side : 1<A.side) (box : InsideContainer W)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (order : O.s≤A.s) (bottom : B O.c O.s<O.loV+O.side)
    (oa : O.loV+O.side≤lower A (-O.s) O.c)
    (aw : A.loV+A.side≤lower W (-A.s) A.c ∨
      W.loU+W.side≤lower A W.c W.s)
    (top : W.loV+W.side≤t+(72/25)*W.c) : O.s<t := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have op : 0<O.c := by linarith only [ob.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have dp : 0<W.c := by linarith only [wb.1]
  let D := O.c*A.s-O.s*A.c
  let K := O.c*A.c+O.s*A.s
  let k := A.c*W.c-A.s*t
  let h := A.s*W.c+A.c*t
  let T := A.c+A.s*W.c^2+A.c*W.c*t
  have cosine := cosine_order an on order
  have dnon : 0≤D := by
    have first := mul_nonneg on.1 (sub_nonneg.mpr cosine)
    have second := mul_nonneg op.le (sub_nonneg.mpr order)
    dsimp [D]
    nlinarith only [first,second]
  have kp : 0<K := by
    have first := mul_pos op cp
    have second := mul_nonneg on.1 an.1
    dsimp [K]
    linarith only [first,second]
  have knon : 0≤k := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have hnon : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dp.le) (mul_nonneg cp.le wn.1)
  have tpos : 0<T := by
    have first := mul_nonneg an.1 (sq_nonneg W.c)
    have second := mul_nonneg (mul_nonneg cp.le dp.le) wn.1
    dsimp [T]
    linarith only [cp,first,second]
  have oaForm : lower A (-O.s) O.c=D*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have u : -O.s*A.c+O.c*A.s=D := by dsimp [D]; ring
    have v : -(-O.s)*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg dnon,abs_of_nonneg kp.le]
    ring
  have upperU : A.loU≤2*(A.c+A.s)-1 := by linarith only [cap,side]
  have support : B O.c O.s <
      D*(2*(A.c+A.s)-1)+K*(A.loV+A.side-1) := by
    have first := mul_nonneg dnon (sub_nonneg.mpr upperU)
    have second := mul_nonneg kp.le (sub_nonneg.mpr side.le)
    rw [oaForm] at oa
    nlinarith only [bottom,oa,first,second]
  have wall := FourSquareBLBridge.left_wall W dp.le box
  rw [ws,abs_neg,abs_of_nonneg wn.1] at wall
  dsimp [centerX] at wall
  rw [ws] at wall
  have coupled : W.side*(W.c+t)≤W.c*(W.loU+W.side)+t*(W.loV+W.side) := by
    nlinarith only [wall]
  have wallSide : 1<W.side := by rwa [←sameAW]
  have modes :
      W.c*(A.loV+A.side)≤A.c*(t+(72/25)*W.c)-T ∨
      W.c+t-t^2-(72/25)*W.c*t <
        W.c*(k*(2*(A.c+A.s)-1)-h*(A.loV+A.side)) := by
    rcases aw with central | wallAxis
    · left
      have form : lower W (-A.s) A.c=-h*(W.loU+W.side)+k*W.loV := by
        rw [lower_negative_nonpos W t (-A.s) A.c ws
          (by dsimp [h] at hnon; nlinarith only [hnon])
          (by dsimp [k] at knon; nlinarith only [knon])]
        dsimp [h,k]
        ring
      rw [form] at central
      have sep := mul_le_mul_of_nonneg_left central dp.le
      have container := mul_nonneg hnon (sub_nonneg.mpr coupled)
      have identity :
          W.c*(-h*(W.loU+W.side)+k*W.loV)+
            h*(W.c*(W.loU+W.side)+t*(W.loV+W.side)-W.side*(W.c+t)) =
          A.c*(W.loV+W.side)-W.side*T := by
        dsimp [h,k,T]
        linear_combination (A.c*W.loV)*wn.2.2
      have topWeight := mul_nonneg cp.le (sub_nonneg.mpr top)
      have width := mul_nonneg tpos.le (sub_nonneg.mpr wallSide.le)
      clear_value D K k h T
      nlinarith only [sep,container,identity,topWeight,width]
    · right
      have form : lower A W.c W.s=k*A.loU-h*(A.loV+A.side) := by
        rw [ws,lower_in_bands]
        have u : W.c*A.c+(-t)*A.s=k := by dsimp [k]; ring
        have v : -W.c*A.s+(-t)*A.c=-h := by dsimp [h]; ring
        rw [u,v,abs_of_nonneg knon,abs_of_nonpos (neg_nonpos.mpr hnon)]
        ring
      rw [form] at wallAxis
      have sep := mul_le_mul_of_nonneg_left wallAxis dp.le
      have capWeight := mul_nonneg (mul_nonneg dp.le knon) (sub_nonneg.mpr upperU)
      have topWeight := mul_nonneg wn.1 (sub_nonneg.mpr top)
      have width := mul_pos (sub_pos.mpr wallSide)
        (show 0<W.c+t by linarith only [dp,wn.1])
      clear_value D K k h T
      nlinarith only [coupled,sep,capWeight,topWeight,width]
  apply lt_of_not_ge
  intro outer
  have transferred := lower_transfer on wn an outer order support
  apply endpoint_obstruction wn an (le_trans outer order) transferred northwest
  exact modes

/-- Actual point ownership and pairwise separation give the angle comparison
under the additional explicit wall exclusion at (1,2.88). The latter still
requires an original-packing entrance for C696/C977. -/
theorem angle_order (O A W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (an : Normal A.c A.s) (wn : Normal W.c t)
    (ws : W.s=-t) (sameOA : O.side=A.side) (sameAW : A.side=W.side)
    (side : 1<A.side) (oBox : InsideContainer O) (wBox : InsideContainer W)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (oMissingCorner : ¬O.Inside 1 1) (oMissingMarker : ¬O.Inside 2 (457/500))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aLeft : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (cap : A.loU+A.side≤2*(A.c+A.s)) (aMissingLeft : ¬A.Inside 1 2)
    (aMissingNW : ¬A.Inside (33/20) (47/20)) (aForeignLow : ¬A.Inside 1 (8/5))
    (wMarker : W.Inside (457/500) 2) (wPoint : W.Inside 1 (113/50))
    (wHigh : W.Inside 1 (12/5)) (wMissingTop : ¬W.Inside 1 (72/25))
    (oaApart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (awApart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) : O.s<t := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have op : 0<O.c := by linarith only [ob.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have canonical : |O.s|≤O.c := by rw [abs_of_nonneg on.1]; exact on.2.1
  have oa := PositiveCentralTransverse.only_bottom_axis O A op canonical an sameOA
    side oBox oMarker oNear oFar oMissingCorner oMissingMarker
    aMarker aD aLeft aLow cap aMissingLeft oaApart
  have leftCap := PositiveCentralLeftBand.upper_face A side cp an.1 cap
    aMarker aLeft aMissingLeft
  have order := PositiveCentralPositiveBottom.own_axis_angle O A on an sameOA
    side oBox oMarker oNear oMissingCorner oMissingMarker aLeft leftCap oa
  have northwest := PositiveCentralLeftBand.northwest_cap A side cp an.1 an.2.1
    aLeft aLow aMissingNW aForeignLow
  have faces := C696PositiveCorner.corner_faces O on
    (by rwa [sameOA]) oBox oMarker oNear oMissingCorner oMissingMarker
  have pB : O.c*B O.c O.s=O.c-2*O.c*O.s+O.s-O.s^2 := by
    dsimp [B]
    field_simp [op.ne']
    ring
  have oldBoundary : O.c*C696CornerMargins.boundary O.c O.s=
      O.c+O.s-2*O.c*O.s-(457/500)*O.s^2 := by
    unfold C696CornerMargins.boundary
    field_simp [op.ne']
  have weaker : B O.c O.s≤C696CornerMargins.boundary O.c O.s := by
    have scaled : 0≤O.c*(C696CornerMargins.boundary O.c O.s-B O.c O.s) := by
      nlinarith only [pB,oldBoundary,sq_nonneg O.s]
    have gap := nonneg_of_mul_nonneg_right scaled op
    linarith only [gap]
  have bottom := lt_of_le_of_lt weaker faces.2.2.2.2
  have aw := NegativeWallTopSeed.alternatives A W t an wn ws sameAW side cap
    aLeft aLow aMarker wMarker wHigh awApart
  have top := NegativeWallTopSeed.upper_face A W t an wn ws sameAW side cap
    aLeft aLow aMarker wMarker wPoint wHigh wMissingTop awApart
  exact support_order O A W t on an wn ws sameOA sameAW side wBox cap northwest
    order.le bottom oa aw top

end N12Compact.PositiveCentralEscapeOrder
