import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! The continuous scalar margin for the central square's longitudinal
separating axis. Normal order reduces the central angle to two endpoints.
The remaining wall interval has one positive quartic certificate. -/
namespace N12Compact.CentralWallParallelMargin

open C977CornerCubic
set_option Elab.async false

private theorem ordered_dot {c s C S P Q : ℝ}
    (hn : Normal c s) (h : Normal C S) (order : 0≤c*S-s*C)
    (hp : 0≤P) (hpq : P≤Q) : P*c+Q*s≤P*C+Q*S := by
  classical
  have b := normal_bounds hn
  have B := normal_bounds h
  have product := mul_nonneg order
    (add_nonneg
      (mul_nonneg (show 0≤c by linarith only [b.1]) h.1)
      (mul_nonneg hn.1 (show 0≤C by linarith only [B.1])))
  have difference : (c*S-s*C)*(c*S+s*C)=S^2-s^2 := by
    linear_combination S^2*hn.2.2-s^2*h.2.2
  have vertical : s≤S := by
    by_contra no
    have strict : S<s := lt_of_not_ge no
    have positive := mul_pos (sub_pos.mpr strict)
      (show 0<s+S by linarith only [strict,h.1])
    nlinarith only [positive,product,difference]
  have correction := mul_nonneg (sub_nonneg.mpr vertical)
    (show 0≤c+C-S-s by linarith only [hn.2.1,h.2.1])
  have identity : (c+C)*(C+S-c-s)=(S-s)*(c+C-S-s) := by
    linear_combination h.2.2-hn.2.2
  have scaled : 0≤(c+C)*(C+S-c-s) := by rw [identity]; exact correction
  have sum : 0≤C+S-c-s := nonneg_of_mul_nonneg_right scaled
    (by linarith only [b.1,B.1] : 0<c+C)
  have first := mul_nonneg hp sum
  have second := mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr vertical)
  nlinarith only [first,second]

private noncomputable def quartic (q : ℝ) : ℝ :=
  -72+(6873/50)*q+(1471151/10000)*q^2-(5027/50)*q^3-(208849/10000)*q^4

/-- Five nonnegative terms cover the entire interval, including endpoints. -/
private theorem quartic_nonneg {q : ℝ} (lo : 5/12≤q) (hi : q≤1) :
    0≤quartic q := by
  have x : 0≤q-5/12 := sub_nonneg.mpr lo
  have y : 0≤1-q := sub_nonneg.mpr hi
  have p0 := pow_nonneg y 4
  have p1 := mul_nonneg x (pow_nonneg y 3)
  have p2 := mul_nonneg (sq_nonneg (q-5/12)) (sq_nonneg (1-q))
  have p3 := mul_nonneg (pow_nonneg x 3) y
  have p4 := pow_nonneg x 4
  have identity : 24010000*quartic q =
      604136975*(1-q)^4+
      26807920080*(q-5/12)*(1-q)^3+
      76776711696*(q-5/12)^2*(1-q)^2+
      69975280512*(q-5/12)^3*(1-q)+
      18900905472*(q-5/12)^4 := by unfold quartic; ring
  nlinarith only [identity,p0,p1,p2,p3,p4]

private theorem wall_endpoint {r t : ℝ} (h : Normal r t)
    (large : 5*r≤12*t) :
    0≤7*r+17*t-11-(457/100)*(t/r) := by
  have b := normal_bounds h
  have rp : 0<r := by linarith only [b.1]
  let q := t/r
  have lo : 5/12≤q := (le_div_iff₀ rp).mpr (by linarith only [large])
  have hi : q≤1 := (div_le_one rp).mpr h.2.1
  have qpos : 0≤q := le_trans (by norm_num) lo
  have unit : (1/r)^2=1+q^2 := by
    dsimp [q]
    field_simp [ne_of_gt rp] <;> nlinarith only [h.2.2]
  have polynomial := quartic_nonneg lo hi
  have identity : (7+17*q)^2-((11+(457/100)*q)*(1/r))^2=quartic q := by
    calc
      _ = (7+17*q)^2-(11+(457/100)*q)^2*(1/r)^2 := by ring
      _ = (7+17*q)^2-(11+(457/100)*q)^2*(1+q^2) := by rw [unit]
      _ = quartic q := by unfold quartic; ring
  have small : (11+(457/100)*q)*(1/r)≤7+17*q := by
    by_contra no
    have strict := lt_of_not_ge no
    have product := mul_pos (sub_pos.mpr strict)
      (show 0<(11+(457/100)*q)*(1/r)+(7+17*q) by
        linarith only [strict,qpos])
    nlinarith only [product,identity,polynomial]
  have product := mul_nonneg rp.le (sub_nonneg.mpr small)
  have identity2 : r*((7+17*q)-(11+(457/100)*q)*(1/r)) =
      7*r+17*t-11-(457/100)*(t/r) := by
    dsimp [q]
    field_simp [ne_of_gt rp] <;> ring
  linarith only [product,identity2]

theorem parallel_margin {c s r t : ℝ} (hn : Normal c s) (hw : Normal r t)
    (shallow : 12*s≤5*c) (order : 0≤c*t-s*r) :
    0≤1+(c-s)*r+(c+s)*t-2*c-(457/500)*s*(t/r) := by
  classical
  have b := normal_bounds hw
  have rp : 0<r := by linarith only [b.1]
  let P := 2-r-t
  let Q := r-t+(457/500)*(t/r)
  have pnonneg : 0≤P := by dsimp [P]; linarith only [b.2.2.2.2.2]
  have qTimes : r*Q=r*(r-t)+(457/500)*t := by
    dsimp [Q]
    field_simp [ne_of_gt rp] <;> ring
  have qOrder : P≤Q := by
    have half : 2*r*t≤1 := by nlinarith only [hw.2.2,sq_nonneg (r-t)]
    have gap : 0≤(457/500)*(1+r)-2*r*t := by linarith only [half,b.1]
    have positive := mul_nonneg hw.1 gap
    have identity : r*(1+r)*(Q-P)=t*((457/500)*(1+r)-2*r*t) := by
      calc
        _ = (1+r)*(r*Q-r*P) := by ring
        _ = t*((457/500)*(1+r)-2*r*t) := by
          rw [qTimes]
          dsimp [P]
          linear_combination 2*r*hw.2.2
    have scale : 0<r*(1+r) := mul_pos rp (by linarith only [rp])
    have scaled : 0≤r*(1+r)*(Q-P) := by rw [identity]; exact positive
    have nonnegative : 0≤Q-P := nonneg_of_mul_nonneg_right scaled scale
    exact sub_nonneg.mp nonnegative
  have endpoint : P*c+Q*s≤1 := by
    by_cases small : 12*t≤5*r
    · have dominance := ordered_dot hn hw order pnonneg qOrder
      have rb : 12/13≤r := by
        by_contra no
        have below : r<12/13 := lt_of_not_ge no
        have first := mul_nonneg (show 0≤5*r-12*t by linarith only [small])
          (show 0≤5*r+12*t by linarith only [rp,hw.1])
        have second := mul_pos (sub_pos.mpr below)
          (show 0<12/13+r by linarith only [rp])
        nlinarith only [first,second,hw.2.2]
      have first := mul_nonneg (show 0≤1-r by linarith only [b.2.1])
        (show 0≤2*r-(457/500)*(1+r) by linarith only [rb])
      have identity : r*(1-P*r-Q*t)=(1-r)*(2*r-(457/500)*(1+r)) := by
        calc
          _ = r-r^2*P-t*(r*Q) := by ring
          _ = (1-r)*(2*r-(457/500)*(1+r)) := by
            rw [qTimes]
            dsimp [P]
            linear_combination (r-457/500)*hw.2.2
      have scaled : 0≤r*(1-P*r-Q*t) := by rw [identity]; exact first
      have nonnegative : 0≤1-P*r-Q*t := nonneg_of_mul_nonneg_right scaled rp
      have bound : 0≤1-(P*r+Q*t) := by convert nonnegative using 1 <;> ring
      exact dominance.trans (sub_nonneg.mp bound)
    · have fixed : Normal (12/13 : ℝ) (5/13) := by
        constructor
        · norm_num
        constructor <;> norm_num
      have dominance := ordered_dot hn fixed
        (show 0≤c*(5/13)-s*(12/13) by linarith only [shallow]) pnonneg qOrder
      have margin := wall_endpoint hw (by linarith only [small])
      have identity : 13*(1-P*(12/13)-Q*(5/13)) =
          7*r+17*t-11-(457/100)*(t/r) := by dsimp [P,Q]; ring
      have scaled : 0≤13*(1-P*(12/13)-Q*(5/13)) := by
        rw [identity]
        exact margin
      have nonnegative : 0≤1-P*(12/13)-Q*(5/13) :=
        nonneg_of_mul_nonneg_right scaled (by norm_num : (0:ℝ)<13)
      have bound : 0≤1-(P*(12/13)+Q*(5/13)) := by
        convert nonnegative using 1 <;> ring
      exact dominance.trans (sub_nonneg.mp bound)
  have identity : 1+(c-s)*r+(c+s)*t-2*c-(457/500)*s*(t/r)=1-P*c-Q*s := by
    dsimp [P,Q]; ring
  rw [identity]
  convert sub_nonneg.mpr endpoint using 1 <;> ring

end N12Compact.CentralWallParallelMargin
