import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Exact all-angle shallow-A/B margins. The one quartic is displayed
explicitly, including its interval and a positive decomposition. -/
namespace N12Compact.C849ShallowMargins

private theorem coordinate_bounds (p q : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) : p≤1 ∧ q≤1 := by
  constructor <;> nlinarith only [unit,sq_nonneg p,sq_nonneg q,
    sq_nonneg (p-1),sq_nonneg (q-1)]

private theorem quartic (t : ℝ) (lo : 0≤t) (hi : t≤2/5) :
    0 < 1/50-(19/250)*t-(16/25)*t^2+(819/250)*t^3-(99/50)*t^4 := by
  let z := t-1/5
  have zl : -(1/5)≤z := by dsimp [z]; linarith only [lo]
  have zh : z≤1/5 := by dsimp [z]; linarith only [hi]
  have interval := mul_nonneg (show 0≤z+1/5 by linarith only [zl])
    (show 0≤1/5-z by linarith only [zh])
  have factor : 0≤21260+42300*z-49500*z^2 := by
    dsimp [z] at zl interval ⊢
    nlinarith only [zl,interval]
  have positive := mul_nonneg (sq_nonneg z) factor
  have identity :
      25000*(1/50-(19/250)*t-(16/25)*t^2+(819/250)*t^3-(99/50)*t^4) =
        56*(1-z)+z^2*(21260+42300*z-49500*z^2) := by dsimp [z]; ring
  dsimp [z] at identity positive zh
  nlinarith only [identity,positive,zh]

private theorem half_angle_margin (p q : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (slope : q≤(4/5)*p) :
    0 < p+(4/5)*q-(49/50)*p^2-(419/500)*p*q-(13/20)*q^2 := by
  obtain ⟨pHigh,qHigh⟩ := coordinate_bounds p q hp hq unit
  have denominator : 0<1+p := by linarith only [hp]
  let t := q/(1+p)
  have tLow : 0≤t := div_nonneg hq denominator.le
  have tHigh : t≤2/5 := by
    apply (div_le_iff₀ denominator).mpr
    linarith only [slope,pHigh]
  have positive := quartic t tLow tHigh
  have pIdentity : p*(1+t^2)=1-t^2 := by
    dsimp [t]
    field_simp [ne_of_gt denominator]
    linear_combination (p+1)*unit
  have qIdentity : q*(1+t^2)=2*t := by
    dsimp [t]
    field_simp [ne_of_gt denominator]
    linear_combination q*(p+1)*unit
  have identity :
      (p+(4/5)*q-(49/50)*p^2-(419/500)*p*q-(13/20)*q^2)*(1+t^2)^2 =
        1/50-(19/250)*t-(16/25)*t^2+(819/250)*t^3-(99/50)*t^4 := by
    calc
      _ = (p*(1+t^2))*(1+t^2)+(4/5)*(q*(1+t^2))*(1+t^2)-
          (49/50)*(p*(1+t^2))^2-(419/500)*(p*(1+t^2))*(q*(1+t^2))-
          (13/20)*(q*(1+t^2))^2 := by ring
      _ = _ := by rw [pIdentity,qIdentity]; ring
  have factor : 0 < (1+t^2)^2 := sq_pos_of_pos (by nlinarith only [sq_nonneg t])
  exact (mul_pos_iff_of_pos_right factor).mp (identity.symm ▸ positive)

/-- A lower-V mode, or the stronger lower-U mode, when the relative
angle is nonpositive. The actual angle hypotheses imply the half-angle
interval [0,2/5], including both endpoints. -/
theorem lowerV_b_neg (p q c s : ℝ)
    (hp : 0<p) (hq : 0≤q) (unit : p^2+q^2=1)
    (hc : 0<c) (hs : 0≤s) (slope : s≤(4/5)*c)
    (cross : c*q-s*p≤0) :
    0 < (c*p+s*q)*(1-(7/10)*(p+q))+
      (c*q-s*p)*((7/20)*p-(9/100)*q) := by
  have product := mul_nonneg hp.le (sub_nonneg.mpr slope)
  have aSlope : q≤(4/5)*p := by
    by_contra failure
    have positive := mul_pos hc (sub_pos.mpr (lt_of_not_ge failure))
    nlinarith only [cross,product,positive]
  let F := p-(7/10)*p^2-(7/20)*p*q-(9/100)*q^2
  let G := q-(7/20)*p^2-(61/100)*p*q-(7/10)*q^2
  have qOrder : q≤p := by linarith only [aSlope,hp]
  have orderSquare := mul_nonneg (sub_nonneg.mpr qOrder) (add_nonneg hp.le hq)
  have pLow : 7/10≤p := by
    nlinarith only [unit,orderSquare,hp,sq_nonneg (p-7/10)]
  have product' := mul_nonneg hq (sub_nonneg.mpr pLow)
  have gNegative : G≤0 := by
    dsimp [G]
    nlinarith only [unit,product',hq,sq_nonneg (7*q-6)]
  have positive : 0<F+(4/5)*G := by
    have h := half_angle_margin p q hp.le hq unit aSlope
    dsimp [F,G]
    nlinarith only [h]
  have scaled := mul_pos hc positive
  have slack := mul_nonneg (sub_nonneg.mpr slope) (neg_nonneg.mpr gNegative)
  dsimp [F,G] at scaled gNegative slack
  nlinarith only [scaled,slack]

/-- The opposite missing-marker mode has a direct quadratic margin;
the missing marker itself supplies q≥3/7. -/
theorem lowerU_b_pos (p q c s : ℝ)
    (hp : 0≤p) (hq : 3/7≤q) (unit : p^2+q^2=1)
    (hc : 0<c) (slope : s≤(4/5)*c) :
    0 < (c*p+s*q)+(c*q-s*p)+(7/10)*(c*q-s*p)*(p-q)+
      (c*p+s*q)*((1/20)*p-(27/20)*q) := by
  have qNonneg : 0≤q := by linarith only [hq]
  obtain ⟨pHigh,qHigh⟩ := coordinate_bounds p q hp qNonneg unit
  let F := p+q+(1/20)*p^2-(13/20)*p*q-(7/10)*q^2
  let G := q-p-(7/10)*p^2+(3/4)*p*q-(27/20)*q^2
  have product := mul_nonneg hp (sub_nonneg.mpr qHigh)
  have gNegative : G≤0 := by
    dsimp [G]
    nlinarith only [unit,product,hp,sq_nonneg (13*q-10)]
  have interval := mul_nonneg (show 0≤q-53/127 by linarith only [hq])
    (sub_nonneg.mpr qHigh)
  have extra := mul_nonneg hp (show 0≤1/5-q/20 by linarith only [qHigh])
  have positive : 0<F+(4/5)*G := by
    dsimp [F,G]
    nlinarith only [unit,interval,extra]
  have scaled := mul_pos hc positive
  have slack := mul_nonneg (sub_nonneg.mpr slope) (neg_nonneg.mpr gNegative)
  dsimp [F,G] at scaled slack
  nlinarith only [scaled,slack]

/-- The original top marker of B controls its lower projection onto A.
This consumes both actual ratio bounds of the shallow positive sector. -/
theorem lowerU_a_pos (p q c s : ℝ)
    (hp : 0≤p) (hq : 0≤q) (unit : p^2+q^2=1)
    (hc : 0<c) (hs : 0≤s) (unitB : c^2+s^2=1)
    (lowSlope : 3*c≤7*s) (highSlope : s≤(4/5)*c) :
    0 < 1+(1/20)*p-(27/20)*q+
      (c*q-s*p)*((7/20)*c+(92/125)*s) := by
  have loSquare := mul_nonneg (sub_nonneg.mpr lowSlope)
    (show 0≤7*s+3*c by linarith only [hc,hs])
  have hiSquare := mul_nonneg (sub_nonneg.mpr highSlope)
    (show 0≤(4/5)*c+s by linarith only [hc,hs])
  have cHigh : c≤23/25 := by
    nlinarith only [unitB,loSquare,hc,sq_nonneg (c-23/25)]
  have cSquare : 3/5≤c^2 := by nlinarith only [unitB,hiSquare]
  have sSquare : s^2≤2/5 := by nlinarith only [unitB,cSquare]
  have difference : c-s≤92/175 := by linarith only [lowSlope,cHigh]
  have order : s≤c := by linarith only [highSlope,hc]
  have diffSquare := mul_nonneg (show 0≤92/175-(c-s) by linarith only [difference])
    (show 0≤92/175+(c-s) by linarith only [order])
  have productLow : 9/25≤c*s := by nlinarith only [unitB,diffSquare]
  have productHigh : c*s≤1/2 := by nlinarith only [unitB,sq_nonneg (c-s)]
  have first : s*((7/20)*c+(92/125)*s)-1/20≤21/50 := by
    nlinarith only [sSquare,productHigh]
  have second : 27/20-c*((7/20)*c+(92/125)*s)≤22/25 := by
    nlinarith only [cSquare,productLow]
  have wp := mul_le_mul_of_nonneg_left first hp
  have wq := mul_le_mul_of_nonneg_left second hq
  have short : (21/50)*p+(22/25)*q<1 := by
    nlinarith only [unit,sq_nonneg ((22/25)*p-(21/50)*q),
      sq_nonneg ((21/50)*p+(22/25)*q-1)]
  nlinarith only [wp,wq,short]

end N12Compact.C849ShallowMargins
