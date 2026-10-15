import Compact.Geometry.C1092ShallowPositiveScalars
import Compact.Geometry.C1092WallPolynomial

/-! Complete bottom-envelope scalar intervals, including the previously
unported interval beyond the initial quarter turn. Everything is proved by
continuous rational factors on 0≤z≤1, with the aligned edge retained. -/
namespace N12Compact.C1092ShallowBottom
open C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

theorem bottomQ_full (x z : ℝ) (xn : 0 ≤ x) (xu : x ≤ 1/4)
    (zn : 0 ≤ z) (zu : z ≤ 1) : 11/32 ≤ bottomQ x z := by
  have z2 : z^2 ≤ 1 := by simpa using power_le_bound zn zu 2
  have x2 : x^2 ≤ 1/16 := by have h:=power_le_bound xn xu 2; norm_num at h; exact h
  have x3 : x^3 ≤ 1/64 := by have h:=power_le_bound xn xu 3; norm_num at h; exact h
  have W : 0 ≤ 1+z+5*z^2+z^3 := by nlinarith only [zn,sq_nonneg z,pow_nonneg zn 3]
  have weight := mul_nonneg (show 0≤1/4-x by linarith only [xu]) W
  have base : 1/2 ≤ (1+z+z^2+z^3)-x*(1+z+5*z^2+z^3) := by
    nlinarith only [weight,z2,zn,pow_nonneg zn 3]
  have first := mul_nonneg (sq_nonneg x)
    (show 0≤z^3-z^2+5*z+1 by nlinarith only [z2,zn,pow_nonneg zn 3])
  have last := mul_nonneg (pow_nonneg xn 3)
    (show 0≤z^3-z^2+z+1 by nlinarith only [z2,zn,pow_nonneg zn 3])
  dsimp [bottomQ]
  nlinarith only [base,first,last,x2,x3]

theorem bottomP_full (x z : ℝ) (xn : 0 ≤ x) (xu : x ≤ 1/4)
    (zn : 0 ≤ z) (zu : z ≤ 1) : 0 < bottomP x z := by
  have baseline := C1092WallPolynomial.cubic_taylor_nonneg
    (14/5) (-22) 53 (-22) (1/4) z zu (by norm_num) (by norm_num) (by norm_num)
  have b0 : 0 < bottomB0 z := by dsimp [bottomB0]; linarith only [baseline]
  have b1 : 0 ≤ bottomB1 z := by
    dsimp [bottomB1]; nlinarith only [zu,sq_nonneg z,pow_nonneg zn 3]
  have both : 0 ≤ 4*bottomB1 z+bottomB2 z := by
    dsimp [bottomB1,bottomB2]
    nlinarith only [zu,sq_nonneg z,pow_nonneg zn 3]
  have b3 : 0 ≤ bottomB3 z := by
    dsimp [bottomB3]; nlinarith only [zn,sq_nonneg z,pow_nonneg zn 3]
  have first := mul_nonneg (mul_nonneg xn (show 0≤1-4*x by linarith only [xu])) b1
  have second := mul_nonneg (sq_nonneg x) both
  have last := mul_nonneg (pow_nonneg xn 3) b3
  have identity : bottomP x z=bottomB0 z+x*(1-4*x)*bottomB1 z+
      x^2*(4*bottomB1 z+bottomB2 z)+x^3*bottomB3 z := by dsimp [bottomP]; ring
  rw [identity]
  linarith only [b0,first,second,last]

theorem lower_nonneg (a x z : ℝ) (xp : 0 < x) (xu : x ≤ 1/4)
    (zn : 0 ≤ z) (zu : z ≤ 1) (ha : a ≤ cosH x+(11/25)*sinH x)
    (angle : x*z+x+z ≤ 1) : 0 ≤ bottomMinus a x z := by
  have P := bottomP_full x z xp.le xu zn zu
  have Q := bottomQ_full x z xp.le xu zn zu
  have factor : x*z+x+z-1 ≤ 0 := by linarith only [angle]
  have slope : bottomSlope x z ≤ 0 := by
    rw [bottom_slope_factor x z xp]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg factor (by linarith only [Q])) (by positivity)
  have base : 0 ≤ bottomMinus (cosH x+(11/25)*sinH x) x z := by
    rw [bottom_side_endpoint x z xp]
    exact div_nonneg (mul_nonneg (neg_nonneg.mpr factor) P.le) (by positivity)
  rw [bottom_affine a (cosH x+(11/25)*sinH x)]
  exact add_nonneg base (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ha) slope)

def upperBase (x z : ℝ) : ℝ :=
  z*(1-z)^2+x*z*(1-z^2)+x^2*(1+4*z-z^2+4*z^3)+
    x^3*(1-2*z+z^2-4*z^3)+2*x^4*(-1+z-z^2+z^3)

def upperWeight (x z : ℝ) : ℝ :=
  (1+z+z^2+z^3)+x*(2+z+z^3)+x^2*(2+z+2*z^2-z^3)+
    x^3*(1+2*z-z^2+2*z^3)+x^4*(1+z^2-2*z^3)+
    x^5*(-1+z-z^2+z^3)

theorem upper_polynomials (x z : ℝ) (xp : 0 < x) (xu : x ≤ 1/4)
    (zn : 0 ≤ z) (zu : z ≤ 1) : 0 < upperBase x z ∧ 0 < upperWeight x z := by
  have z2 : z^2 ≤ 1 := by simpa using power_le_bound zn zu 2
  have z3 : z^3 ≤ z^2 := by
    have h:=mul_nonneg (sq_nonneg z) (sub_nonneg.mpr zu)
    nlinarith only [h]
  have x2 : x^2 ≤ 1/16 := by have h:=power_le_bound xp.le xu 2; norm_num at h; exact h
  have x5 : x^5 ≤ 1/1024 := by have h:=power_le_bound xp.le xu 5; norm_num at h; exact h
  have first := mul_nonneg zn (sq_nonneg (1-z))
  have second := mul_nonneg (mul_nonneg xp.le zn) (show 0≤1-z^2 by linarith only [z2])
  have cubic := mul_nonneg (pow_nonneg zn 3) (show 0≤1-x by linarith only [xu])
  have square := mul_nonneg xp.le (sq_nonneg (1-z))
  have tail := mul_nonneg (sq_nonneg x)
    (show 0≤2-(1-z)*(1+z^2) by nlinarith only [zn,zu,z2,pow_nonneg zn 3])
  have arc := mul_nonneg zn (show 0≤4-z by linarith only [zu])
  have bracket : 0 < 1+4*z-z^2+4*z^3+x*(1-2*z+z^2-4*z^3)+
      2*x^2*(-1+z-z^2+z^3) := by
    nlinarith only [cubic,square,tail,arc,x2]
  have positive := mul_pos (sq_pos_of_pos xp) bracket
  have base : 0 < upperBase x z := by
    dsimp [upperBase]
    nlinarith only [first,second,positive]
  have w1 := mul_nonneg xp.le
    (show 0≤2+z+z^3 by nlinarith only [zn,pow_nonneg zn 3])
  have w2 := mul_nonneg (sq_nonneg x)
    (show 0≤2+z+2*z^2-z^3 by nlinarith only [zn,z3,sq_nonneg z])
  have w3 := mul_nonneg (pow_nonneg xp.le 3)
    (show 0≤1+2*z-z^2+2*z^3 by nlinarith only [zn,z2,pow_nonneg zn 3])
  have w4 := mul_nonneg (pow_nonneg xp.le 4)
    (show 0≤1+z^2-2*z^3 by nlinarith only [z2,z3])
  have w5 := mul_nonneg (pow_nonneg xp.le 5)
    (show 0≤1+z-z^2+z^3 by nlinarith only [zn,z2,pow_nonneg zn 3])
  have weight : 0 < upperWeight x z := by
    dsimp [upperWeight]
    nlinarith only [w1,w2,w3,w4,w5,x5,zn,sq_nonneg z,pow_nonneg zn 3]
  exact ⟨base,weight⟩

def upper (a x z : ℝ) : ℝ :=
  -cosH z*((scalarB a x-sinH x-2*cosH x)/sinH x)-2*sinH z+
    a*wallWeight z/2-
    ((sinH x*sinH z-cosH x*cosH z)*(-sinH x/2)+
      (sinH x*cosH z+cosH x*sinH z)*(sinH x-a)-
      a*(sinH x*sinH z-cosH x*cosH z))

theorem upper_factor (a x z : ℝ) (xp : 0 < x) :
    upper a x z=(x*z+x+z-1)*upperBase x z/((1+x^2)^2*(1+z^2)^2)+
      (a-1)*(x*z+x+z-1)*upperWeight x z/(x*(1+x^2)^2*(1+z^2)^2) := by
  dsimp [upper,upperBase,upperWeight,scalarB,wallWeight,cosH,sinH]
  field_simp [xp.ne',(half_den_pos x).ne',(half_den_pos z).ne']
  <;> ring

theorem upper_nonneg (a x z : ℝ) (ha : 1 ≤ a) (xp : 0 < x) (xu : x ≤ 1/4)
    (zn : 0 ≤ z) (zu : z ≤ 1) (angle : 1 ≤ x*z+x+z) : 0 ≤ upper a x z := by
  obtain ⟨base,weight⟩ := upper_polynomials x z xp xu zn zu
  have factor : 0 ≤ x*z+x+z-1 := by linarith only [angle]
  rw [upper_factor a x z xp]
  apply add_nonneg
  · exact div_nonneg (mul_nonneg factor base.le) (by positivity)
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) factor) weight.le) (by positivity)

#print axioms lower_nonneg
#print axioms upper_nonneg
end
end N12Compact.C1092ShallowBottom
