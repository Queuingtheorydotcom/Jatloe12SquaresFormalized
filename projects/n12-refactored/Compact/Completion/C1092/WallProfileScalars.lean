import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The continuous two-angle envelope of the direct corner-to-wall transfer.
The actual sign of the relative normal splits two cubics; four nonnegative
coefficients prove each cubic on its whole interval. No angle partition,
numerical certificate or canonical restriction is used. -/
namespace N12Compact.C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def half (c s : ℝ) : ℝ := s/(1+c)
def profile (c s : ℝ) : ℝ := c-s*(c+s)/(1+c)

theorem quarter_data (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) :
    0 ≤ half c s ∧ half c s ≤ 1 ∧ half c s*(1+c)=s ∧
      (1+(half c s)^2)*c=1-(half c s)^2 ∧
      (1+(half c s)^2)*s=2*half c s := by
  have cp : 0 < 1+c := by linarith only [hc]
  have sone : s ≤ 1 := by nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
  let z := half c s
  have zn : 0 ≤ z := div_nonneg hs cp.le
  have zu : z ≤ 1 := (div_le_iff₀ cp).mpr (by linarith only [sone,hc])
  have relation : z*(1+c)=s := by dsimp [z,half]; field_simp [cp.ne']
  have relation_sq := congrArg (fun a : ℝ => a^2) relation
  dsimp at relation_sq
  have zero : (1+c)*((1+c)*(1+z^2)-2)=0 := by
    nlinarith only [relation_sq,unit]
  have denominator : (1+c)*(1+z^2)=2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left cp.ne')
  have cform : (1+z^2)*c=1-z^2 := by nlinarith only [denominator]
  have sform : (1+z^2)*s=2*z := by
    calc
      _ = (1+z^2)*(z*(1+c)) := by rw [relation]
      _ = z*((1+c)*(1+z^2)) := by ring
      _ = 2*z := by rw [denominator]; ring
  exact ⟨zn,zu,relation,cform,sform⟩

private theorem cubic (a b c d z : ℝ) (zn : 0 ≤ z) (zu : z ≤ 1)
    (h0 : 0 ≤ 3*a) (h1 : 0 ≤ 3*a+b) (h2 : 0 ≤ 3*a+2*b+c)
    (h3 : 0 ≤ 3*(a+b+c+d)) : 0 ≤ a+b*z+c*z^2+d*z^3 := by
  have rest : 0 ≤ 1-z := sub_nonneg.mpr zu
  have first := mul_nonneg h0 (pow_nonneg rest 3)
  have second := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) h1) zn)
    (sq_nonneg (1-z))
  have third := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) h2)
    (sq_nonneg z)) rest
  have last := mul_nonneg h3 (pow_nonneg zn 3)
  have identity : 3*(a+b*z+c*z^2+d*z^3)=
      3*a*(1-z)^3+3*(3*a+b)*z*(1-z)^2+
        3*(3*a+2*b+c)*z^2*(1-z)+3*(a+b+c+d)*z^3 := by ring
  nlinarith only [first,second,third,last,identity]

private def plus (x y : ℝ) : ℝ :=
  y^2*(2-y)+2*x*(1-y-y^2)+x^2*(-2-4*y+4*y^2-y^3)+2*y*x^3

private def minus (x y : ℝ) : ℝ :=
  -1+3*y^2-y^3+2*x*(1+y-y^2)+x^2*(-1-4*y+3*y^2-y^3)+2*y*x^3

private theorem coefficient_bounds (y : ℝ) (yn : 0 ≤ y) (yu : y ≤ 1) :
    0 ≤ 2+y^3*(13+13*y-y^2-3*y^3) ∧
    0 ≤ 2*(1-y)+4*y^2+8*y^3+10*y^4+y^5*(6-4*y) ∧
    0 ≤ y^2*(8+18*y+y^2*(14-2*y^2)+2*y^3) ∧
    0 ≤ y^2*(12-2*y^4+22*y+6*y^2*(1-y)) := by
  have y2 : y^2 ≤ 1 := by
    have h := mul_le_mul yu yu yn (by norm_num : (0:ℝ)≤1)
    simpa only [pow_two,one_mul] using h
  have y3 : y^3 ≤ 1 := by
    have h := mul_le_mul y2 yu yn (by norm_num : (0:ℝ)≤1)
    simpa only [pow_succ,one_mul] using h
  have y4 : y^4 ≤ 1 := by
    have h := mul_le_mul y2 y2 (sq_nonneg y) (by norm_num : (0:ℝ)≤1)
    nlinarith only [h]
  have first := mul_nonneg (pow_nonneg yn 3)
    (show 0 ≤ 13+13*y-y^2-3*y^3 by linarith only [y2,y3,yn])
  have second := mul_nonneg (pow_nonneg yn 5)
    (show 0 ≤ 6-4*y by linarith only [yu])
  have third := mul_nonneg (sq_nonneg y)
    (show 0 ≤ 14-2*y^2 by linarith only [y2])
  have fourth := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr yu)
  refine ⟨by linarith only [first],?_,?_,?_⟩
  · nlinarith only [second,sub_nonneg.mpr yu,sq_nonneg y,
      pow_nonneg yn 3,pow_nonneg yn 4]
  · exact mul_nonneg (sq_nonneg y)
      (by nlinarith only [third,yn,pow_nonneg yn 3])
  · exact mul_nonneg (sq_nonneg y)
      (by nlinarith only [y4,yn,fourth])

private theorem plus_nonneg (x y : ℝ) (xn : 0 ≤ x) (yn : 0 ≤ y) (yu : y ≤ 1)
    (order : x*(1+y) ≤ 1-y) : 0 ≤ plus x y := by
  by_cases endpoint : y=1
  · have zero : x=0 := by rw [endpoint] at order; linarith only [xn,order]
    rw [zero,endpoint]
    norm_num [plus]
  have yp : 0 < 1-y := by
    apply lt_of_not_ge; intro no; apply endpoint; linarith only [yu,no]
  have wp : 0 < 1+y := by linarith only [yn]
  let z := x*(1+y)/(1-y)
  have zn : 0 ≤ z := div_nonneg (mul_nonneg xn wp.le) yp.le
  have zu : z ≤ 1 := (div_le_iff₀ yp).mpr (by simpa only [one_mul] using order)
  have xform : x=z*(1-y)/(1+y) := by dsimp [z]; field_simp [yp.ne',wp.ne']
  let a := y^2*(2-y)*(1+y)^3
  let b := 2*(1-y-y^2)*(1-y)*(1+y)^2
  let c := (-2-4*y+4*y^2-y^3)*(1-y)^2*(1+y)
  let d := 2*y*(1-y)^3
  have coeff := coefficient_bounds y yn yu
  have h0 : 0 ≤ 3*a := by
    have body : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (mul_nonneg (sq_nonneg y)
        (by linarith only [yu])) (pow_nonneg wp.le 3)
    exact mul_nonneg (by norm_num) body
  have h1 : 0 ≤ 3*a+b := by
    have identity : 3*a+b=2+y^3*(13+13*y-y^2-3*y^3) := by dsimp [a,b]; ring
    rw [identity]; exact coeff.1
  have h2 : 0 ≤ 3*a+2*b+c := by
    have identity : 3*a+2*b+c=
        2*(1-y)+4*y^2+8*y^3+10*y^4+y^5*(6-4*y) := by dsimp [a,b,c]; ring
    rw [identity]; exact coeff.2.1
  have h3 : 0 ≤ 3*(a+b+c+d) := by
    have identity : 3*(a+b+c+d)=6*y^3*(3-y)*(1+y^2) := by dsimp [a,b,c,d]; ring
    rw [identity]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg yn 3))
      (by linarith only [yu])) (by nlinarith only [sq_nonneg y])
  have positive := cubic a b c d z zn zu h0 h1 h2 h3
  have identity : (1+y)^3*plus x y=a+b*z+c*z^2+d*z^3 := by
    rw [xform]
    dsimp [plus,a,b,c,d]
    field_simp [wp.ne']
    <;> ring
  exact nonneg_of_mul_nonneg_right (by rwa [identity]) (pow_pos wp 3)

private theorem minus_nonneg (x y : ℝ) (xu : x ≤ 1) (yn : 0 ≤ y) (yu : y ≤ 1)
    (order : 1-y ≤ x*(1+y)) : 0 ≤ minus x y := by
  by_cases endpoint : y=0
  · have one : x=1 := by rw [endpoint] at order; linarith only [xu,order]
    rw [one,endpoint]
    norm_num [minus]
  have yp : 0 < 2*y := by
    apply lt_of_not_ge; intro no; apply endpoint; linarith only [yn,no]
  have wp : 0 < 1+y := by linarith only [yn]
  let z := (x*(1+y)-(1-y))/(2*y)
  have zn : 0 ≤ z := div_nonneg (sub_nonneg.mpr order) yp.le
  have zu : z ≤ 1 := (div_le_iff₀ yp).mpr (by nlinarith only [xu,wp])
  have xform : x=((1-y)+2*y*z)/(1+y) := by dsimp [z]; field_simp [yp.ne',wp.ne']
  let A := -1+3*y^2-y^3
  let B := 2*(1+y-y^2)
  let C := -1-4*y+3*y^2-y^3
  let D := 2*y
  let a := A*(1+y)^3+B*(1-y)*(1+y)^2+C*(1-y)^2*(1+y)+D*(1-y)^3
  let b := B*(2*y)*(1+y)^2+2*C*(1-y)*(2*y)*(1+y)+3*D*(1-y)^2*(2*y)
  let c := C*(2*y)^2*(1+y)+3*D*(1-y)*(2*y)^2
  let d := D*(2*y)^3
  have coeff := coefficient_bounds y yn yu
  have h0 : 0 ≤ 3*a := by
    have identity : 3*a=6*y^3*(3-y)*(1+y^2) := by dsimp [a,A,B,C,D]; ring
    rw [identity]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg yn 3))
      (by linarith only [yu])) (by nlinarith only [sq_nonneg y])
  have h1 : 0 ≤ 3*a+b := by
    have identity : 3*a+b=y^2*(8+18*y+y^2*(14-2*y^2)+2*y^3) := by
      dsimp [a,b,A,B,C,D]; ring
    rw [identity]; exact coeff.2.2.1
  have h2 : 0 ≤ 3*a+2*b+c := by
    have identity : 3*a+2*b+c=y^2*(12-2*y^4+22*y+6*y^2*(1-y)) := by
      dsimp [a,b,c,A,B,C,D]; ring
    rw [identity]; exact coeff.2.2.2
  have h3 : 0 ≤ 3*(a+b+c+d) := by
    have identity : 3*(a+b+c+d)=6*y^2*(2-y)*(1+y)^3 := by
      dsimp [a,b,c,d,A,B,C,D]; ring
    rw [identity]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg y))
      (by linarith only [yu])) (pow_nonneg wp.le 3)
  have positive := cubic a b c d z zn zu h0 h1 h2 h3
  have identity : (1+y)^3*minus x y=a+b*z+c*z^2+d*z^3 := by
    rw [xform]
    dsimp [minus,a,b,c,d,A,B,C,D]
    field_simp [wp.ne']
    <;> ring
  exact nonneg_of_mul_nonneg_right (by rwa [identity]) (pow_pos wp 3)

theorem envelope (c s r t : ℝ) (cn : 0 ≤ c) (sn : 0 ≤ s)
    (rn : 0 ≤ r) (tn : 0 ≤ t) (cu : c^2+s^2=1) (ru : r^2+t^2=1) :
    profile c s ≤ c*t+s*r+max (c*r-s*t) 0+s*t/(1+r)-(3/2)*s := by
  let x := half r t
  let y := half c s
  have hx := quarter_data r t rn tn ru
  have hy := quarter_data c s cn sn cu
  have dx : 0 < 1+x^2 := by nlinarith only [sq_nonneg x]
  have dy : 0 < 1+y^2 := by nlinarith only [sq_nonneg y]
  have cp : 0 < 1+c := by linarith only [cn]
  have kappa : (c+s)/(1+c)=(1+2*y-y^2)/2 := by
    apply (div_eq_iff cp.ne').mpr
    dsimp [y] at hy ⊢
    nlinarith only [hy.2.2.1,hy.2.2.2.1]
  have angle : (1+x^2)*(1+y^2)*(c*r-s*t)=
      (1-y-x*(1+y))*(1+y+x*(1-y)) := by
    calc
      _ = ((1+y^2)*c)*((1+x^2)*r)-((1+y^2)*s)*((1+x^2)*t) := by ring
      _ = (1-y^2)*(1-x^2)-(2*y)*(2*x) := by
        rw [hy.2.2.2.1,hy.2.2.2.2,hx.2.2.2.1,hx.2.2.2.2]
      _ = _ := by ring
  have last : 0 < 1+y+x*(1-y) := by
    have product := mul_nonneg hx.1 (sub_nonneg.mpr hy.2.1)
    dsimp [x,y] at product ⊢
    linarith only [product,hy.1]
  have tau : s*t/(1+r)=s*x := by dsimp [x,half]; ring
  rw [tau]
  by_cases sign : 0 ≤ c*r-s*t
  · rw [max_eq_left sign]
    have order : x*(1+y) ≤ 1-y := by
      have scaled := mul_nonneg (mul_nonneg dx.le dy.le) sign
      rw [angle] at scaled
      have first := nonneg_of_mul_nonneg_left scaled last
      linarith only [first]
    have p := plus_nonneg x y hx.1 hy.1 hy.2.1 order
    have first : (1+x^2)*(r+t-1)=1-x^2+2*x-(1+x^2) := by
      nlinarith only [hx.2.2.2.1,hx.2.2.2.2]
    have second : (1+x^2)*(r-t+x-3/2+(1+2*y-y^2)/2)=
        1-x^2-2*x+(1+x^2)*(x-3/2+(1+2*y-y^2)/2) := by
      nlinarith only [hx.2.2.2.1,hx.2.2.2.2]
    have identity : (1+x^2)*(1+y^2)*(c*t+s*r+(c*r-s*t)+s*x-(3/2)*s-profile c s)=plus x y := by
      calc
        _ = ((1+y^2)*c)*((1+x^2)*(r+t-1))+
            ((1+y^2)*s)*((1+x^2)*(r-t+x-3/2+(1+2*y-y^2)/2)) := by
          dsimp [profile]
          rw [show s*(c+s)/(1+c)=s*((c+s)/(1+c)) by ring,kappa]
          ring
        _ = _ := by rw [first,second,hy.2.2.2.1,hy.2.2.2.2]; dsimp [plus]; ring
    have nonneg := nonneg_of_mul_nonneg_right (show 0≤(1+x^2)*(1+y^2)*
        (c*t+s*r+(c*r-s*t)+s*x-(3/2)*s-profile c s) by rwa [identity]) (mul_pos dx dy)
    linarith only [nonneg]
  · rw [max_eq_right (lt_of_not_ge sign).le,add_zero]
    have order : 1-y ≤ x*(1+y) := by
      have scaled := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg dx.le dy.le) (lt_of_not_ge sign).le
      rw [angle] at scaled
      have first := nonpos_of_mul_nonpos_left scaled last
      linarith only [first]
    have p := minus_nonneg x y hx.2.1 hy.1 hy.2.1 order
    have first : (1+x^2)*(t-1)=2*x-(1+x^2) := by nlinarith only [hx.2.2.2.2]
    have second : (1+x^2)*(r+x-3/2+(1+2*y-y^2)/2)=
        1-x^2+(1+x^2)*(x-3/2+(1+2*y-y^2)/2) := by
      nlinarith only [hx.2.2.2.1]
    have identity : (1+x^2)*(1+y^2)*(c*t+s*r+s*x-(3/2)*s-profile c s)=minus x y := by
      calc
        _ = ((1+y^2)*c)*((1+x^2)*(t-1))+
            ((1+y^2)*s)*((1+x^2)*(r+x-3/2+(1+2*y-y^2)/2)) := by
          dsimp [profile]
          rw [show s*(c+s)/(1+c)=s*((c+s)/(1+c)) by ring,kappa]
          ring
        _ = _ := by rw [first,second,hy.2.2.2.1,hy.2.2.2.2]; dsimp [minus]; ring
    have nonneg := nonneg_of_mul_nonneg_right (show 0≤(1+x^2)*(1+y^2)*
        (c*t+s*r+s*x-(3/2)*s-profile c s) by rwa [identity]) (mul_pos dx dy)
    linarith only [nonneg]

theorem boundary_cap (c s p q : ℝ) (cn : 0 ≤ c) (sn : 0 ≤ s)
    (pn : 0 ≤ p) (qn : 0 ≤ q) (cu : c^2+s^2=1) (pu : p^2+q^2=1) :
    c*(2-p-half p q)-s*q+min (c*q-s*p) 0 ≤ profile c s := by
  let x := half p q
  let y := half c s
  have hx := quarter_data p q pn qn pu
  have hy := quarter_data c s cn sn cu
  have dx : 0 < 1+x^2 := by nlinarith only [sq_nonneg x]
  have dy : 0 < 1+y^2 := by nlinarith only [sq_nonneg y]
  have cp : 0 < 1+c := by linarith only [cn]
  have cone : c ≤ 1 := by nlinarith only [cu,sq_nonneg s,sq_nonneg (c-1)]
  have sone : s ≤ 1 := by nlinarith only [cu,sq_nonneg c,sq_nonneg (s-1)]
  have sum : 1 ≤ c+s := by
    nlinarith only [cu,mul_nonneg cn sn,cn,sn,sq_nonneg (c+s-1)]
  have form : profile c s=2*c-1-c*y := by
    dsimp [profile,y,half]
    field_simp [cp.ne']
    nlinarith only [cu]
  have angle : (1+x^2)*(1+y^2)*(c*q-s*p)=2*(x-y)*(1+x*y) := by
    calc
      _ = ((1+y^2)*c)*((1+x^2)*q)-((1+y^2)*s)*((1+x^2)*p) := by ring
      _ = (1-y^2)*(2*x)-(2*y)*(1-x^2) := by
        rw [hy.2.2.2.1,hy.2.2.2.2,hx.2.2.2.1,hx.2.2.2.2]
      _ = _ := by ring
  have last : 0 < 2*(1+x*y) := by
    have product := mul_nonneg hx.1 hy.1
    dsimp [x,y] at product ⊢
    linarith only [product]
  change c*(2-p-x)-s*q+min (c*q-s*p) 0 ≤ profile c s
  by_cases sign : 0 ≤ c*q-s*p
  · rw [min_eq_right sign,add_zero]
    have scaled := mul_nonneg (mul_nonneg dx.le dy.le) sign
    rw [angle,show 2*(x-y)*(1+x*y)=(x-y)*(2*(1+x*y)) by ring] at scaled
    have order : 0 ≤ x-y := nonneg_of_mul_nonneg_left scaled last
    have cross : 0 ≤ 1-c*x := by
      have product := mul_le_mul cone hx.2.1 hx.1 (by norm_num : (0:ℝ)≤1)
      dsimp [x] at product ⊢
      nlinarith only [product]
    have remainder := mul_nonneg (sub_nonneg.mpr hx.2.1) cross
    have bracket : 0 ≤ c*x^2-(1+c)*x+c+s := by nlinarith only [remainder,sum]
    have nonneg := mul_nonneg order bracket
    have identity : (1+x^2)*(profile c s-(c*(2-p-x)-s*q))=
        (x-y)*(c*x^2-(1+c)*x+c+s) := by
      calc
        _ = -(1+x^2)*(1+c*y)+c*((1+x^2)*p)+c*x*(1+x^2)+s*((1+x^2)*q) := by
          rw [form]; ring
        _ = _ := by
          rw [hx.2.2.2.1,hx.2.2.2.2,←hy.2.2.1]
          dsimp [x,y]
          linear_combination hy.2.2.2.1
    have nonneg' := nonneg_of_mul_nonneg_right (show 0≤(1+x^2)*
        (profile c s-(c*(2-p-x)-s*q)) by rwa [identity]) dx
    linarith only [nonneg']
  · rw [min_eq_left (lt_of_not_ge sign).le]
    have scaled := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg dx.le dy.le) (lt_of_not_ge sign).le
    rw [angle,show 2*(x-y)*(1+x*y)=(x-y)*(2*(1+x*y)) by ring] at scaled
    have order : 0 ≤ y-x := by
      have first := nonpos_of_mul_nonpos_left scaled last
      linarith only [first]
    have inner : 0 ≤ 1+s+c*(1-x) := by
      have product := mul_nonneg cn (sub_nonneg.mpr hx.2.1)
      linarith only [sn,product]
    have bracket : 0 ≤ -c*x^2+(1+c+s)*x+1-s := by
      have product := mul_nonneg hx.1 inner
      nlinarith only [product,sone]
    have nonneg := mul_nonneg order bracket
    have identity : (1+x^2)*(profile c s-(c*(2-p-x)-s*q+(c*q-s*p)))=
        (y-x)*(-c*x^2+(1+c+s)*x+1-s) := by
      calc
        _ = -(1+x^2)*(1+c*y)+(c+s)*((1+x^2)*p)+
            c*x*(1+x^2)+(s-c)*((1+x^2)*q) := by rw [form]; ring
        _ = _ := by
          rw [hx.2.2.2.1,hx.2.2.2.2,←hy.2.2.1]
          dsimp [x,y]
          linear_combination (1-half p q)*hy.2.2.2.1
    have nonneg' := nonneg_of_mul_nonneg_right (show 0≤(1+x^2)*
        (profile c s-(c*(2-p-x)-s*q+(c*q-s*p))) by rwa [identity]) dx
    linarith only [nonneg']

#print axioms envelope
#print axioms boundary_cap
end
end N12Compact.C1092WallProfileScalars
