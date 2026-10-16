import Compact.Geometry.C977NegativeCorner

/-! One complete support reduction for the positive-central left-point
escape. A negative canonical bottom square cannot separate from the central
square on the central transverse axis. Its own transverse axis remains;
the actual left singleton is needed to address that remaining branch. -/
namespace N12Compact.PositiveCentralNegativeBottom

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem coefficient_bound {c t C S : ℝ}
    (hn : Normal c t) (h : Normal C S) :
    c*(2-c-t)*C+t*(c+t-457/500)*S≤c := by
  have b := normal_bounds hn
  have B := normal_bounds h
  have hc : 0<c := by linarith only [b.1]
  let F := c*(2-c-t)
  let G := t*(c+t-457/500)
  change F*C+G*S≤c
  by_cases small : t≤9/20
  · have fp : 0≤F := mul_nonneg hc.le
      (show 0≤2-c-t by linarith only [b.2.2.2.2.2])
    have gp : 0≤G := mul_nonneg hn.1
      (show 0≤c+t-457/500 by linarith only [b.2.2.2.2.1])
    have correction := mul_nonneg hn.1
      (show 0≤457/500-2*t by linarith only [small])
    have sum : F+G≤c := by
      dsimp [F,G]
      nlinarith only [hn.2.2,b.2.1,correction]
    have first := mul_nonneg fp (show 0≤1-C by linarith only [B.2.1])
    have second := mul_nonneg gp (show 0≤1-S by linarith only [B.2.2.2.1])
    nlinarith only [sum,first,second]
  · have fBound : F≤(17/20)*c := by
      have product := mul_nonneg hc.le
        (show 0≤17/20-(2-c-t) by linarith only [small,b.1])
      dsimp [F]
      nlinarith only [product]
    have gBound : G≤(13/25)*c := by
      have first := mul_nonneg hn.1
        (show 0≤13/25-(c+t-457/500) by linarith only [b.2.2.2.2.2])
      have second := mul_nonneg (sub_nonneg.mpr hn.2.1)
        (show 0≤(13/25:ℝ) by norm_num)
      dsimp [G]
      nlinarith only [first,second]
    have short : (17/20)*C+(13/25)*S<1 := by
      nlinarith only [h.2.2,sq_nonneg (C-17/20),sq_nonneg (S-13/25)]
    have first := mul_nonneg (show 0≤C by linarith only [B.1])
      (sub_nonneg.mpr fBound)
    have second := mul_nonneg h.1 (sub_nonneg.mpr gBound)
    have strict := mul_pos hc (sub_pos.mpr short)
    nlinarith only [first,second,strict]

/-- The full bottom wall and the real bottom marker force this support
strictly above the level needed by a central square missing (1,2).
No corner-missing premise or saved pose enclosure is needed. -/
theorem upper_axis (O : OpenSquare) (t C S : ℝ) (os : O.s=-t)
    (hn : Normal O.c t) (h : Normal C S)
    (side : 1<O.side) (box : InsideContainer O)
    (marker : O.Inside 1 (457/500)) :
    2*C-S < upper O (-S) C+O.side := by
  have b := normal_bounds hn
  have B := normal_bounds h
  have hc : 0<O.c := by linarith only [b.1]
  let K := O.c*C-t*S
  let D := O.c*S+t*C
  let E := K*(O.c+t)+O.c
  have kp : 0≤K := by
    have first := mul_nonneg hc.le (sub_nonneg.mpr h.2.1)
    have second := mul_nonneg h.1 (sub_nonneg.mpr hn.2.1)
    dsimp [K]
    nlinarith only [first,second]
  have dp : 0≤D := add_nonneg (mul_nonneg hc.le h.1)
    (mul_nonneg hn.1 (show 0≤C by linarith only [B.1]))
  have ep : 0<E := by
    have product := mul_nonneg kp
      (show 0≤O.c+t by linarith only [hc,hn.1])
    dsimp [E]
    linarith only [product,hc]
  have form : upper O (-S) C = -D*O.loU+K*(O.loV+O.side) := by
    rw [upper_negative_nonpos O t (-S) C os
      (show -S*O.c-C*t≤0 by dsimp [D] at dp; nlinarith only [dp])
      (show 0≤-S*t+C*O.c by dsimp [K] at kp; nlinarith only [kp])]
    dsimp [K,D]
    ring
  have bottom := ThreeSquare.bottom_wall O hc.le box
  have sabs : |O.s|=t := by rw [os,abs_neg,abs_of_nonneg hn.1]
  have wall : t*(O.loU+O.side)≤O.c*O.loV := by
    rw [sabs] at bottom
    dsimp [centerY] at bottom
    rw [os] at bottom
    nlinarith only [bottom]
  have marked := (negative_bands O t _ _ os).mp marker
  have wallTerm := mul_nonneg kp (sub_nonneg.mpr wall)
  have markerTerm := mul_nonneg h.1
    (show 0≤O.c-(457/500)*t-O.loU by linarith only [marked.1])
  have strict := mul_pos ep (sub_pos.mpr side)
  have scalar := coefficient_bound hn h
  have identity : O.c*(upper O (-S) C+O.side-(2*C-S)) =
      K*(O.c*O.loV-t*(O.loU+O.side))+
      S*(O.c-(457/500)*t-O.loU)+E*(O.side-1)+
      (O.c-(O.c*(2-O.c-t)*C+t*(O.c+t-457/500)*S)) := by
    rw [form]
    dsimp [K,D,E]
    linear_combination (-S*O.loU)*hn.2.2
  have positive : 0<O.c*(upper O (-S) C+O.side-(2*C-S)) := by
    clear_value K D E
    linarith only [identity,wallTerm,markerTerm,strict,scalar]
  have difference := pos_of_mul_pos_right positive hc.le
  linarith only [difference]

theorem central_axis_impossible (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (hn : Normal O.c t) (h : Normal A.c A.s)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (marker : O.Inside 1 (457/500))
    (cap : A.loV+A.side≤2*A.c-A.s) :
    ¬upper O (-A.s) A.c≤A.loV := by
  have bound := upper_axis O t A.c A.s os hn h
    (by rw [same]; exact side) box marker
  rw [same] at bound
  intro separator
  linarith only [bound,cap,separator]

end N12Compact.PositiveCentralNegativeBottom
