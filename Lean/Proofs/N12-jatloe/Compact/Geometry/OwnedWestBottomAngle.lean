import Compact.Geometry.PositiveCentralLeftBand
import Compact.Geometry.PositiveCentralTransverse

/-! The actual owned-west central square rules out the steep negative
bottom-marker escape. The remaining marker face forces a shallow bottom
angle. This argument retains both full O/A transverse selectors and uses
no sign or placement assumption on the left singleton. Source only,
uncompiled. -/
namespace N12Compact.OwnedWestBottomAngle

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

/-- A genuine upper-V escape at the next bottom marker lies on the
steep arc, separated continuously from the shallow upper-U escape. -/
theorem upper_v_spread {c t : ℝ} (normal : Normal c t)
    (escape : boundary c t<2*t+(457/500)*c) :
    47/100<t ∧ 27/20<c+t := by
  have b := normal_bounds normal
  have cp : 0<c := by linarith only [b.1]
  have boundaryExact : c*boundary c t=c+c*t+t-t^2 := by
    unfold boundary
    field_simp [cp.ne']
    ring
  have multiplied := mul_lt_mul_of_pos_left escape cp
  have negative : c-457/500+t*(1-c)-(43/500)*t^2<0 := by
    nlinarith only [multiplied,boundaryExact,normal.2.2]
  have steep : 47/100<t := by
    by_contra failure
    have small : t≤47/100 := le_of_not_gt failure
    have square := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤47/100+t by linarith only [normal.1])
    have wide : 22/25≤c := by
      by_contra no
      have product := mul_nonneg (show 0≤22/25-c by linarith only [no])
        (show 0≤22/25+c by linarith only [cp])
      nlinarith only [square,product,normal.2.2]
    have upperDefect : 1-c≤(25/47)*t^2 := by
      have product := mul_nonneg (sub_nonneg.mpr b.2.1)
        (show 0≤c-22/25 by linarith only [wide])
      nlinarith only [product,normal.2.2]
    have lowerDefect : t^3/2≤t*(1-c) := by
      have product := mul_nonneg normal.1 (sq_nonneg (1-c))
      have identity : t*(1-c)-t^3/2=t*(1-c)^2/2 := by
        linear_combination (-t/2)*normal.2.2
      nlinarith only [identity,product]
    let T : ℝ := 47/100
    let B : ℝ := 14521/23500
    have squareSmall := mul_nonneg normal.1 (sub_nonneg.mpr small)
    have coefficient : 0≤B*(T+t)-(T^2+T*t+t^2)/2 := by
      have first := mul_nonneg
        (show 0≤B-T by dsimp [B,T]; norm_num)
        (show 0≤T+t by dsimp [T]; linarith only [normal.1])
      have second := mul_nonneg (show 0≤T by dsimp [T]; norm_num)
        (show 0≤T+t by dsimp [T]; linarith only [normal.1])
      dsimp [T] at first second ⊢
      nlinarith only [first,second,squareSmall]
    have product := mul_nonneg (show 0≤T-t by dsimp [T]; linarith only [small]) coefficient
    have identity : 43/500-B*t^2+t^3/2=
        14141/10000000+(T-t)*(B*(T+t)-(T^2+T*t+t^2)/2) := by
      dsimp [B,T]
      ring
    have positive : 0<43/500-B*t^2+t^3/2 := by
      nlinarith only [identity,product]
    dsimp [B] at positive
    nlinarith only [negative,upperDefect,lowerDefect,positive]
  have spread : 27/20<c+t := by
    by_contra no
    have sum : c+t≤27/20 := le_of_not_gt no
    have top : t≤27/40 := by linarith only [normal.2.1,sum]
    have interval := mul_nonneg
      (show 0≤t-47/100 by linarith only [steep]) (sub_nonneg.mpr top)
    have product := mul_nonneg (show 0≤27/20-t-c by linarith only [sum])
      (show 0≤27/20-t+c by linarith only [normal.2.1])
    nlinarith only [interval,product,normal.2.2,steep]
  exact ⟨steep,spread⟩

private theorem central_bounds {C S : ℝ} (normal : Normal C S)
    (slope : 13*S≤7*C) : 43/50≤C ∧ S≤1/2 := by
  have b := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr slope)
    (show 0≤7*C+13*S by linarith only [b.1,normal.1])
  have small : S≤1/2 := by
    by_contra no
    have square := mul_nonneg (show 0≤S-1/2 by linarith only [no])
      (show 0≤S+1/2 by linarith only [normal.1])
    nlinarith only [product,square,normal.2.2]
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/2+S by linarith only [normal.1])
  have wide : 43/50≤C := by
    by_contra no
    have csquare := mul_nonneg (show 0≤43/50-C by linarith only [no])
      (show 0≤43/50+C by linarith only [b.1])
    nlinarith only [square,csquare,normal.2.2]
  exact ⟨wide,small⟩

private theorem central_remainder {c t C S : ℝ}
    (on : Normal c t) (an : Normal C S) (wide : 43/50≤C) (small : S≤1/2) :
    (c+t)*((1-C)-(7/20)*S^2)-(c-t)*S*(1-(7/20)*C)≤19/280 := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0≤c := by linarith only [ob.1]
  have ap : 0≤C := by linarith only [ab.1]
  have defect : 1-C≤(27/50)*S^2 := by
    have product := mul_nonneg (sub_nonneg.mpr ab.2.1)
      (show 0≤(27/50)*(1+C)-1 by linarith only [wide])
    have identity : (27/50)*S^2-(1-C)=
        (1-C)*((27/50)*(1+C)-1) := by
      linear_combination (27/50)*an.2.2
    nlinarith only [identity,product]
  have first := mul_nonneg (add_nonneg cp on.1) (sub_nonneg.mpr defect)
  have second := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr on.2.1) an.1)
    (show 0≤1-(7/20)*C by linarith only [ab.2.1])
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/2+S by linarith only [an.1])
  have third := mul_nonneg (add_nonneg cp on.1)
    (show 0≤1/4-S^2 by nlinarith only [square])
  nlinarith only [first,second,third,ob.2.2.2.2.2]

/-- The two actual central caps uniformly bound its support on O's V
axis. The residual is below 19/280 over the entire owned-west arc. -/
theorem own_axis_impossible (O A : OpenSquare) (t : ℝ)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (side : 1≤A.side) (wide : 43/50≤A.c) (small : A.s≤1/2)
    (steep : 47/100<t) (spread : 27/20<O.c+t)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (face : boundary O.c t<O.loV+O.side)
    (sep : O.loV+O.side≤lower A t O.c) : False := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<O.c := by linarith only [ob.1]
  have ap : 0≤A.c := by linarith only [ab.1]
  let H := t*A.c+O.c*A.s
  let K := O.c*A.c-t*A.s
  have hp : 0≤H := add_nonneg (mul_nonneg on.1 ap) (mul_nonneg cp.le an.1)
  have kp : 0≤K := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,second]
  have form : lower A t O.c=H*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have u : t*A.c+O.c*A.s=H := rfl
    have v : -t*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg hp,abs_of_nonneg kp]
    ring
  have first := mul_nonneg hp (sub_nonneg.mpr cap)
  have second := mul_nonneg kp (sub_nonneg.mpr northwest)
  have width := mul_nonneg (sub_nonneg.mpr side) (add_nonneg hp kp)
  have identity : H*(2*(A.c+A.s))+K*((47/20)*A.c-(33/20)*A.s)-H-K=
      t+(27/20)*O.c+(O.c+t)*((1-A.c)-(7/20)*A.s^2)-
        (O.c-t)*A.s*(1-(7/20)*A.c) := by
    dsimp [H,K]
    linear_combination (2*t+(47/20)*O.c)*an.2.2
  have residual := central_remainder on an wide small
  have upper : lower A t O.c≤t+(27/20)*O.c+19/280 := by
    clear_value H K
    nlinarith only [form,first,second,width,identity,residual]
  have boundaryExact : O.c*boundary O.c t=O.c+O.c*t+t-t^2 := by
    unfold boundary
    field_simp [cp.ne']
    ring
  have square := mul_nonneg (show 0≤t-47/100 by linarith only [steep])
    (show 0≤t+47/100 by linarith only [on.1])
  have gap : 0<O.c*(boundary O.c t-(t+(27/20)*O.c+19/280)) := by
    nlinarith only [boundaryExact,on.2.2,spread,square,ob.2.1]
  have positive := pos_of_mul_pos_right gap cp.le
  linarith only [positive,upper,face,sep]

/-- The other actual transverse separator is impossible on the same
steep arc, using the bottom wall and the original O marker. -/
theorem central_axis_impossible (O A : OpenSquare) (t : ℝ)
    (os : O.s=-t) (on : Normal O.c t) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1≤O.side) (spread : 27/20<O.c+t)
    (floor : t*(O.loU+O.side)≤O.c*O.loV)
    (marker : O.Inside 1 (457/500))
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (sep : upper O (-A.s) A.c≤A.loV) : False := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<O.c := by linarith only [ob.1]
  have ap : 0<A.c := by linarith only [ab.1]
  let K := O.c*A.c-t*A.s
  let H := O.c*A.s+t*A.c
  have kp : 0≤K := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,second]
  have hp : 0≤H := add_nonneg (mul_nonneg cp.le an.1) (mul_nonneg on.1 ap.le)
  have form : upper O (-A.s) A.c= -H*O.loU+K*(O.loV+O.side) := by
    rw [upper_in_bands,os]
    have u : (-A.s)*O.c+A.c*(-t)= -H := by dsimp [H]; ring
    have v : -(-A.s)*(-t)+A.c*O.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg kp]
    ring
  have markerU : O.loU<O.c-(457/500)*t := by
    have h := marker.1
    rw [os] at h
    nlinarith only [h]
  have first := mul_nonneg kp (sub_nonneg.mpr floor)
  have second := mul_nonneg an.1 (sub_nonneg.mpr markerU.le)
  have width := mul_nonneg (sub_nonneg.mpr side)
    (show 0≤K*(O.c+t)+O.c by
      nlinarith only [mul_nonneg kp (add_nonneg cp.le on.1),cp])
  let Q := (13/20)*O.c-O.c*t+(457/500)*t-t^2
  have qp : 0≤Q := by
    have replace := mul_nonneg on.1
      (show 0≤(717/500)-(O.c+t) by linarith only [ob.2.2.2.2.2])
    dsimp [Q]
    nlinarith only [replace,on.2.1,cp]
  have third := mul_nonneg an.1 qp
  have fourth := mul_nonneg cp.le (sub_nonneg.mpr ab.2.1)
  have strict := mul_pos (mul_pos cp ap) (sub_pos.mpr spread)
  have identity : O.c*(upper O (-A.s) A.c+O.side-
        ((47/20)*A.c-(33/20)*A.s))=
      K*(O.c*O.loV-t*(O.loU+O.side))+
      A.s*(O.c-(457/500)*t-O.loU)+
      (O.side-1)*(K*(O.c+t)+O.c)+
      O.c*(1-A.c)+O.c*A.c*(O.c+t-27/20)+A.s*Q := by
    rw [form]
    dsimp [K,H,Q]
    linear_combination (-A.s*O.loU)*on.2.2
  have positive : 0<O.c*(upper O (-A.s) A.c+O.side-
      ((47/20)*A.c-(33/20)*A.s)) := by
    clear_value K H Q
    linarith only [identity,first,second,width,third,fourth,strict]
  have gap := pos_of_mul_pos_right positive cp.le
  linarith only [gap,sep,northwest,same]

/-- All original owned-west data force the bottom sine below 1/5.
Both O/A axes and both missing-bottom-marker faces are exhausted. -/
theorem small_bottom (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1) (missingMarker : ¬O.Inside 2 (457/500))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aLeft : A.Inside (3/2) 2) (aLow : A.Inside 2 (3/2))
    (west : A.Inside 1 2) (cap : A.loU+A.side≤2*(A.c+A.s))
    (missingNW : ¬A.Inside (33/20) (47/20)) (foreignLow : ¬A.Inside 1 (8/5))
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) : t<1/5 := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<O.c := by linarith only [ob.1]
  have ap : 0<A.c := by linarith only [ab.1]
  have oSide : 1<O.side := by rwa [same]
  have faces := corner_face O t os on oSide box oMarker oNear oFar missingCorner
  have northwest := PositiveCentralLeftBand.northwest_cap A side ap an.1 an.2.1
    aLeft aLow missingNW foreignLow
  have slope := PositiveCentralLeftBand.left_point_tilt A northwest west
  have bounds := central_bounds an slope.le
  have escape : O.loU+O.side≤2*O.c-(457/500)*t ∨
      O.loV+O.side≤2*t+(457/500)*O.c := by
    by_cases upperU : O.loU+O.side≤2*O.c-(457/500)*t
    · exact Or.inl upperU
    · right
      apply le_of_not_gt
      intro upperV
      apply missingMarker
      apply (negative_bands O t 2 (457/500) os).mpr
      have marker := (negative_bands O t 1 (457/500) os).mp oMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [marker.1,marker.2.2.1,cp,on.1,upperU,upperV]
  rcases escape with upperU | upperV
  · have chord : 1-O.c<(43/500)*t := by
      linarith only [faces.1,upperU,oSide]
    have positive : 0<t := by nlinarith only [chord,ob.2.1]
    have weighted := mul_lt_mul_of_pos_left chord
      (show 0<1+O.c by linarith only [cp])
    have square : t^2<(43/250)*t := by
      have replace := mul_nonneg on.1 (sub_nonneg.mpr ob.2.1)
      nlinarith only [weighted,replace,on.2.2]
    have product : 0<t*(43/250-t) := by nlinarith only [square]
    have gap := pos_of_mul_pos_right product positive.le
    linarith only [gap]
  · have spread := upper_v_spread on (lt_of_lt_of_le faces.2.2 upperV)
    have canonical : |O.s|≤O.c := by
      rw [os,abs_neg,abs_of_nonneg on.1]
      exact on.2.1
    rcases PositiveCentralTransverse.alternatives O A cp canonical an same side
      oNear oFar aMarker aD aLeft aLow cap apart with own | central
    · have sep : O.loV+O.side≤lower A t O.c := by simpa only [os,neg_neg] using own
      exact False.elim (own_axis_impossible O A t on an side.le bounds.1 bounds.2
        spread.1 spread.2 cap northwest faces.2.2 sep)
    · exact False.elim (central_axis_impossible O A t os on an same oSide.le
        spread.2 faces.2.1 oMarker northwest central)

#print axioms upper_v_spread
#print axioms own_axis_impossible
#print axioms central_axis_impossible
#print axioms small_bottom
end N12Compact.OwnedWestBottomAngle
