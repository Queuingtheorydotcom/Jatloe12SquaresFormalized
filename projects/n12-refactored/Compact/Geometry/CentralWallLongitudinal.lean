import Compact.Geometry.CentralWallEscape

/-! Continuous scalar margin for separation on the neighboring wall's
longitudinal axis.  The wall direction is arbitrary in the stated cone;
two exact supporting lines of the unit circle replace angle sampling. -/
namespace N12Compact.CentralWallLongitudinal
open S12 S12Pilot
set_option Elab.async false

noncomputable def X (c s : ℝ) : ℝ := 2+(7/20)*s^2+(7/20)*c*s
noncomputable def Y (c s : ℝ) : ℝ := 33/20+(7/20)*s^2-(7/20)*c*s
noncomputable def margin (c s q w : ℝ) : ℝ :=
  w+(c-s)+q*(c+s)+X c s-4+q*(Y c s-2)-(457/500)*q^2

private theorem normal_bounds (c s : ℝ) (hc : 12/13 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) :
    c ≤ 1 ∧ s ≤ 2/5 ∧ 1-(13/25)*s^2 ≤ c := by
  have cu : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,hc]
  have sl : 0 ≤ (c-12/13)*(c+12/13) := mul_nonneg
    (sub_nonneg.mpr hc) (by linarith only [hc])
  have su : s ≤ 2/5 := by nlinarith only [unit,sl,hs]
  have radial := mul_nonneg (sub_nonneg.mpr cu) (sub_nonneg.mpr hc)
  exact ⟨cu,su,by nlinarith only [unit,radial]⟩

private theorem tangent (c s q w : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hq : 0 ≤ q) (hw : 0 ≤ w) (unit : c^2+s^2=1)
    (normal : w^2=1+q^2) : c+s*q ≤ w := by
  have weighted := congrArg (fun x : ℝ => x*(1+q^2)) unit
  dsimp at weighted
  have square : (c+s*q)^2 ≤ w^2 := by
    nlinarith only [weighted,normal,sq_nonneg (s-c*q)]
  have nonnegative : 0 ≤ c+s*q := add_nonneg hc (mul_nonneg hs hq)
  nlinarith only [square,nonnegative,hw]

private theorem small_margin (c s p q w : ℝ)
    (hc : 12/13 ≤ c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (hp : 0 ≤ p) (angle : c*p=s) (hpq : p ≤ q) (hq : q ≤ 1/2)
    (hw : 0 ≤ w) (normal : w^2=1+q^2) : 0 ≤ margin c s q w := by
  obtain ⟨cu,su,radial⟩ := normal_bounds c s hc hs unit
  let K := -2+(7/20)*s^2+(7/20)*c*s+2*c-s
  let L := -7/20+(7/20)*s^2-(7/20)*c*s+c+2*s
  have sp : s=c*p := angle.symm
  have baseIdentity :
      (1+c)*(K+L*p-(457/500)*p^2) = p^2*((543/500)*c-457/500) := by
    have normal' : c^2+c^2*p^2=1 := by rw [sp] at unit; nlinarith only [unit]
    have difference :
        (1+c)*(K+L*p-(457/500)*p^2)-p^2*((543/500)*c-457/500) =
          ((7/20)*p*(1+c)+2)*(c^2+c^2*p^2-1) := by
      dsimp [K,L]
      rw [sp]
      ring
    rw [normal'] at difference
    nlinarith only [difference]
  have base : 0 ≤ K+L*p-(457/500)*p^2 := by
    have product := mul_nonneg (sq_nonneg p)
      (show 0 ≤ (543/500)*c-457/500 by linarith only [hc])
    by_contra negative
    have bad := mul_neg_of_pos_of_neg
      (show 0 < 1+c by linarith only [hc]) (lt_of_not_ge negative)
    nlinarith only [baseIdentity,product,bad]
  have pbound : p ≤ (13/12)*s := by
    have product := mul_nonneg hp (sub_nonneg.mpr hc)
    nlinarith only [product,angle]
  have csbound := mul_nonneg hs (sub_nonneg.mpr cu)
  have increasing : 0 ≤ L-(457/500)*(q+p) := by
    dsimp [L]
    nlinarith only [hc,hs,sq_nonneg s,csbound,pbound,hq]
  have gain := mul_nonneg (sub_nonneg.mpr hpq) increasing
  have bound : 0 ≤ K+L*q-(457/500)*q^2 := by
    nlinarith only [base,gain]
  have lower := tangent c s q w (by linarith only [hc]) hs
    (le_trans hp hpq) hw unit normal
  dsimp [margin,X,Y,K,L] at *
  linarith only [bound,lower]

private theorem large_margin (c s q w : ℝ)
    (hc : 12/13 ≤ c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (hq : 1/2 ≤ q) (qu : q ≤ 23/20)
    (hw : 0 ≤ w) (normal : w^2=1+q^2) : 0 ≤ margin c s q w := by
  obtain ⟨cu,su,radial⟩ := normal_bounds c s hc hs unit
  let K := -6/5+(7/20)*s^2+(7/20)*c*s+c-s
  let L := 1/4+(7/20)*s^2-(7/20)*c*s+c+s
  let f := fun x : ℝ => K+L*x-(457/500)*x^2
  have cslo := mul_nonneg hs (sub_nonneg.mpr hc)
  have cshi := mul_nonneg hs (sub_nonneg.mpr cu)
  have s2 := mul_nonneg hs (sub_nonneg.mpr su)
  have left : 1/50 ≤ f (1/2) := by
    dsimp [f,K,L]
    nlinarith only [radial,cslo,hs,su,s2]
  have right : 9/1000 ≤ f (23/20) := by
    dsimp [f,K,L]
    nlinarith only [radial,cshi,hs,su,s2]
  have leftWeight := mul_nonneg (sub_nonneg.mpr qu)
    (show 0 ≤ f (1/2)-9/1000 by linarith only [left])
  have rightWeight := mul_nonneg (sub_nonneg.mpr hq)
    (sub_nonneg.mpr right)
  have curve := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr qu)
  have identity :
      (13/20)*(f q-9/1000) =
        (23/20-q)*(f (1/2)-9/1000)+(q-1/2)*(f (23/20)-9/1000)+
          (457/500)*(13/20)*(q-1/2)*(23/20-q) := by
    dsimp [f]
    ring
  have fpositive : 0 ≤ f q := by
    have total : 0 ≤ (13/20)*(f q-9/1000) := by
      rw [identity]
      apply add_nonneg (add_nonneg leftWeight rightWeight)
      have weightedCurve := mul_nonneg
        (show (0 : ℝ) ≤ (457/500)*(13/20) by norm_num) curve
      simpa only [mul_assoc] using weightedCurve
    have lower : 0 ≤ f q-9/1000 :=
      nonneg_of_mul_nonneg_right total (by norm_num : (0 : ℝ) < 13/20)
    exact (by norm_num : (0 : ℝ) ≤ 9/1000).trans (sub_nonneg.mp lower)
  have lower := tangent (4/5) (3/5) q w (by norm_num) (by norm_num)
    (by linarith only [hq]) hw (by norm_num) normal
  dsimp [f,K,L,margin,X,Y] at *
  linarith only [fpositive,lower]

/-- The full wall-axis sector. The variable `p` is the central slope;
`q` is the wall slope and `w` its positive normalization factor. -/
theorem wall_axis_margin (c s p q w : ℝ)
    (hc : 12/13 ≤ c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (hp : 0 ≤ p) (angle : c*p=s) (hpq : p ≤ q) (qu : q ≤ 23/20)
    (hw : 0 ≤ w) (normal : w^2=1+q^2) : 0 ≤ margin c s q w := by
  by_cases half : q ≤ 1/2
  · exact small_margin c s p q w hc hs unit hp angle hpq half hw normal
  · exact large_margin c s q w hc hs unit (lt_of_not_ge half).le qu hw normal

#print axioms wall_axis_margin
end N12Compact.CentralWallLongitudinal
