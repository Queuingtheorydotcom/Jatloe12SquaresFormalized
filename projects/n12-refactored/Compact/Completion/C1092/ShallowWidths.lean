import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! The two square-width bounds used by the actual shallow wall-order
theorem. The boundary orientation is unrestricted within its positive
frame, and both relative orders and their aligned edge are included. -/
namespace N12Compact.C1092ShallowWidths
open C977CornerCubic
set_option Elab.async false

private theorem arc_chord (c s h t A B : ℝ)
    (cn : 0≤c) (sn : 0≤s) (hn : 0≤h) (tn : 0≤t)
    (centralUnit : c^2+s^2=1) (wallUnit : h^2+t^2=1)
    (An : 0≤A) (Dpos : 0≤c*t-s*h)
    (coefficient : A*c≤B*(1+s)) : A≤A*(c*h+s*t)+B*(c*t-s*h) := by
  let k := c*h+s*t
  let D := c*t-s*h
  have kn : 0≤k := add_nonneg (mul_nonneg cn hn) (mul_nonneg sn tn)
  have kp : 0<1+k := by linarith only [kn]
  have denominator : 0<1+s := by linarith only [sn]
  have tOne : t≤1 := by nlinarith only [wallUnit,sq_nonneg h,tn]
  have relativeUnit : k^2+D^2=1 := by
    dsimp [k,D]
    linear_combination (h^2+t^2)*centralUnit+wallUnit
  have endpoint : 0≤c*(1+k)-D*(1+s) := by
    have identity : c*(1+k)-D*(1+s)=c*(1-t)+h*(1+s) := by
      dsimp [k,D]
      linear_combination h*centralUnit
    rw [identity]
    exact add_nonneg (mul_nonneg cn (sub_nonneg.mpr tOne))
      (mul_nonneg hn denominator.le)
  have first := mul_nonneg (sub_nonneg.mpr coefficient) kp.le
  have last := mul_nonneg An endpoint
  have bracket : 0≤B*(1+k)-A*D := by
    apply nonneg_of_mul_nonneg_right _ denominator
    convert add_nonneg first last using 1 <;> ring
  have product := mul_nonneg Dpos bracket
  have result : 0≤A*k+B*D-A := by
    apply nonneg_of_mul_nonneg_right _ kp
    have identity : (1+k)*(A*k+B*D-A)=D*(B*(1+k)-A*D) := by
      linear_combination A*relativeUnit
    rw [identity]
    exact product
  dsimp [k,D] at result
  exact sub_nonneg.mp result

private theorem weighted (c s h t w : ℝ)
    (cn : 0≤c) (sn : 0≤s) (hn : 0≤h) (tn : 0≤t)
    (centralUnit : c^2+s^2=1) (wallUnit : h^2+t^2=1)
    (An : 0≤1+w*(c+s))
    (first : (1+w*(c+s))*c≤(1+w*(c-s))*(1+s))
    (last : (1+w*(c+s))*s≤(1+w*(s-c))*(1+c)) :
    1+w*(c+s)≤w*(h+t)+|c*t-s*h|+c*h+s*t := by
  by_cases order : 0≤c*t-s*h
  · have lower := arc_chord c s h t (1+w*(c+s)) (1+w*(c-s))
      cn sn hn tn centralUnit wallUnit An order first
    rw [abs_of_nonneg order]
    have identity : (1+w*(c+s))*(c*h+s*t)+(1+w*(c-s))*(c*t-s*h)=
        w*(h+t)+(c*t-s*h)+c*h+s*t := by
      linear_combination w*(h+t)*centralUnit
    rwa [identity] at lower
  · have order' : 0≤s*h-c*t := by linarith only [order]
    have lower := arc_chord s c t h (1+w*(c+s)) (1+w*(s-c))
      sn cn tn hn (by nlinarith only [centralUnit])
      (by nlinarith only [wallUnit]) An order' last
    rw [abs_of_nonpos (lt_of_not_ge order).le]
    have identity : (1+w*(c+s))*(s*t+c*h)+(1+w*(s-c))*(s*h-c*t)=
        w*(h+t)-(c*t-s*h)+c*h+s*t := by
      linear_combination w*(h+t)*centralUnit
    rwa [identity] at lower

theorem positive_widths {c s : ℝ} (normal : Normal c s)
    (h t : ℝ) (hn : 0≤h) (tn : 0≤t) (unit : h^2+t^2=1) :
    1+c*(c+s)≤c*(h+t)+|c*t-s*h|+c*h+s*t ∧
      1+s*(c+s)≤s*(h+t)+|c*t-s*h|+c*h+s*t := by
  have bounds := normal_bounds normal
  have cn : 0≤c := by linarith only [bounds.1]
  have sum : 0≤c+s-1 := sub_nonneg.mpr bounds.2.2.2.2.1
  have cDefect : 0≤1-c := sub_nonneg.mpr bounds.2.1
  have sDefect : 0≤1-s := sub_nonneg.mpr bounds.2.2.2.1
  have endpoint0 := mul_nonneg cDefect (add_nonneg cDefect normal.1)
  have endpoint1 := mul_nonneg normal.1 sum
  have endpoint2 := mul_nonneg cn sum
  have endpoint3 := mul_nonneg sDefect (add_nonneg sDefect cn)
  constructor
  · apply weighted c s h t c cn normal.1 hn tn normal.2.2 unit
      (by positivity)
    · have identity : (1+c*(c-s))*(1+s)-(1+c*(c+s))*c=(1-c)*(1-c+s) := by
        linear_combination -c*normal.2.2
      exact sub_nonneg.mp (by rw [identity]; exact endpoint0)
    · have identity : (1+c*(s-c))*(1+c)-(1+c*(c+s))*s=s*(c+s-1) := by
        linear_combination -(1+c)*normal.2.2
      exact sub_nonneg.mp (by rw [identity]; exact endpoint1)
  · apply weighted c s h t s cn normal.1 hn tn normal.2.2 unit
      (by positivity)
    · have identity : (1+s*(c-s))*(1+s)-(1+s*(c+s))*c=c*(c+s-1) := by
        linear_combination -(1+s)*normal.2.2
      exact sub_nonneg.mp (by rw [identity]; exact endpoint2)
    · have identity : (1+s*(s-c))*(1+c)-(1+s*(c+s))*s=(1-s)*(1-s+c) := by
        linear_combination -s*normal.2.2
      exact sub_nonneg.mp (by rw [identity]; exact endpoint3)

theorem signed_widths {c s : ℝ} (normal : Normal c s)
    (a b : ℝ) (unit : a^2+b^2=1) :
    1+c*(c+s)≤c*(|a|+|b|)+|c*b-s*a|+|c*a+s*b| ∧
      1+s*(c+s)≤s*(|a|+|b|)+|c*b-s*a|+|c*a+s*b| := by
  have cn : 0≤c := by linarith only [(normal_bounds normal).1]
  by_cases an : 0≤a
  · by_cases bn : 0≤b
    · have nonnegative := add_nonneg (mul_nonneg cn an) (mul_nonneg normal.1 bn)
      simpa only [abs_of_nonneg an,abs_of_nonneg bn,abs_of_nonneg nonnegative,add_assoc]
        using positive_widths normal a b an bn unit
    · have bn' : b≤0 := (lt_of_not_ge bn).le
      have D : c*b-s*a≤0 := sub_nonpos.mpr
        ((mul_nonpos_of_nonneg_of_nonpos cn bn').trans (mul_nonneg normal.1 an))
      have identity (w : ℝ) :
          w*(|a|+|b|)+|c*b-s*a|+|c*a+s*b|=
            w*((-b)+a)+|c*a-s*(-b)|+c*(-b)+s*a := by
        rw [abs_of_nonneg an,abs_of_nonpos bn',abs_of_nonpos D,
          show c*a-s*(-b)=c*a+s*b by ring]
        ring
      rw [identity c,identity s]
      exact positive_widths normal (-b) a (by linarith only [bn']) an
        (by nlinarith only [unit])
  · have an' : a≤0 := (lt_of_not_ge an).le
    by_cases bn : 0≤b
    · have D : 0≤c*b-s*a := sub_nonneg.mpr
        ((mul_nonpos_of_nonneg_of_nonpos normal.1 an').trans (mul_nonneg cn bn))
      have identity (w : ℝ) :
          w*(|a|+|b|)+|c*b-s*a|+|c*a+s*b|=
            w*(b+(-a))+|c*(-a)-s*b|+c*b+s*(-a) := by
        rw [abs_of_nonpos an',abs_of_nonneg bn,abs_of_nonneg D,
          show c*(-a)-s*b=-(c*a+s*b) by ring,abs_neg]
        ring
      rw [identity c,identity s]
      exact positive_widths normal b (-a) bn (by linarith only [an'])
        (by nlinarith only [unit])
    · have bn' : b≤0 := (lt_of_not_ge bn).le
      have E : c*a+s*b≤0 := add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos cn an')
        (mul_nonpos_of_nonneg_of_nonpos normal.1 bn')
      have identity (w : ℝ) :
          w*(|a|+|b|)+|c*b-s*a|+|c*a+s*b|=
            w*((-a)+(-b))+|c*(-b)-s*(-a)|+c*(-a)+s*(-b) := by
        rw [abs_of_nonpos an',abs_of_nonpos bn',abs_of_nonpos E,
          show c*(-b)-s*(-a)=-(c*b-s*a) by ring,abs_neg]
        ring
      rw [identity c,identity s]
      exact positive_widths normal (-a) (-b) (by linarith only [an'])
        (by linarith only [bn']) (by nlinarith only [unit])

#print axioms positive_widths
#print axioms signed_widths
end N12Compact.C1092ShallowWidths
