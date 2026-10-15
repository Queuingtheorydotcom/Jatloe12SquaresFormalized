import Compact.Geometry.C977CornerSectorBounds

/-! Exact, closed-interval inequalities for POSITIVE-RETAINING-ANGLE-AND-
ORIGINS Theorem1. Unit-circle chords replace derivatives and half-angle
estimates. The weak steep endpoint is t=3/5. -/
namespace N12Compact.C1092MPPMPositiveRetainingSteep.Scalars
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def kappa (c s d t : ℝ) : ℝ := c*d+s*t
def sigma (c s d t : ℝ) : ℝ := c*t-s*d
def uPlus (c s d t : ℝ) : ℝ :=
  1+kappa c s d t-(c+s)-kappa c s d t*d/2-
    (13/50)*sigma c s d t*d
def uMinus (c s d t : ℝ) : ℝ :=
  1-(c+s)+kappa c s d t*(1-d/2)-sigma c s d t
def ePlus (c s d t : ℝ) : ℝ :=
  1+kappa c s d t+sigma c s d t-d/2-
    kappa c s d t*(c+s)+sigma c s d t*((2/5)*s-c)
def eMinus (c s d t : ℝ) : ℝ :=
  1+kappa c s d t-sigma c s d t-d/2-
    kappa c s d t*(c+s)+sigma c s d t*s

theorem canonical_bounds {c s : ℝ} (cn : Normal c s) :
    0<c ∧ c≤1 ∧ 0≤s ∧ s<71/100 ∧ c+s<71/50 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sn : s<71/100 := by
    apply lt_of_not_ge
    intro bad
    have first := mul_nonneg (show 0≤s-71/100 by linarith only [bad])
      (show 0≤s+71/100 by linarith only [cn.1])
    have last := mul_nonneg (sub_nonneg.mpr cn.2.1)
      (show 0≤c+s by linarith only [cp,cn.1])
    nlinarith only [first,last,cn.2.2]
  have sum : c+s<71/50 := by
    apply lt_of_not_ge
    intro bad
    have first := mul_nonneg (show 0≤c+s-71/50 by linarith only [bad])
      (show 0≤c+s+71/50 by linarith only [cp,cn.1])
    nlinarith only [first,sq_nonneg (c-s),cn.2.2]
  exact ⟨cp,cb.2.1,cn.1,sn,sum⟩

theorem relative_unit {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    (kappa c s d t)^2+(sigma c s d t)^2=1 := by
  dsimp [kappa,sigma]
  linear_combination (d^2+t^2)*cn.2.2+en.2.2

/-- These deliberately coarse bounds suffice in both relative orders;
there is no separate near-diagonal trigonometric estimate. -/
theorem relative_bounds {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    7/10<kappa c s d t ∧ kappa c s d t≤1 ∧
      -71/100<sigma c s d t ∧ sigma c s d t<71/100 := by
  have cb := canonical_bounds cn
  have eb := canonical_bounds en
  have kp : 0<kappa c s d t := by
    have first := mul_pos cb.1 eb.1
    have last := mul_nonneg cn.1 en.1
    dsimp [kappa]
    linarith only [first,last]
  have left : -s≤sigma c s d t := by
    have first := mul_nonneg cb.1.le en.1
    have last := mul_nonneg cn.1 (show 0≤1-d by linarith only [eb.2.1])
    dsimp [sigma]
    nlinarith only [first,last]
  have right : sigma c s d t≤t := by
    have first := mul_nonneg en.1 (show 0≤1-c by linarith only [cb.2.1])
    have last := mul_nonneg cn.1 eb.1.le
    dsimp [sigma]
    nlinarith only [first,last]
  have zl : -71/100<sigma c s d t := by linarith only [left,cb.2.2.2.1]
  have zu : sigma c s d t<71/100 := by linarith only [right,eb.2.2.2.1]
  have zu2 := mul_pos (show 0<71/100-sigma c s d t by linarith only [zu])
    (show 0<71/100+sigma c s d t by linarith only [zl])
  have unit := relative_unit cn en
  have low : 7/10<kappa c s d t := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤7/10-kappa c s d t by linarith only [bad])
      (show 0≤7/10+kappa c s d t by linarith only [kp])
    nlinarith only [product,unit,zu2]
  have high : kappa c s d t≤1 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<kappa c s d t-1 by linarith only [bad])
      (show 0<kappa c s d t+1 by linarith only [kp])
    nlinarith only [product,unit,sq_nonneg (sigma c s d t)]
  exact ⟨low,high,zl,zu⟩

theorem steep_bounds {d t : ℝ} (en : Normal d t) (steep : 3/5≤t) :
    d≤4/5 ∧ (3/2)*d+t≤9/5 := by
  have eb := canonical_bounds en
  have product := mul_nonneg (show 0≤t-3/5 by linarith only [steep])
    (show 0≤t+3/5 by linarith only [en.1])
  have cap : d≤4/5 := by
    apply le_of_not_gt
    intro bad
    have last := mul_pos (show 0<d-4/5 by linarith only [bad])
      (show 0<d+4/5 by linarith only [eb.1])
    nlinarith only [last,product,en.2.2]
  have chord := mul_nonneg (show 0≤4/5-d by linarith only [cap])
    (show 0≤(3/2)*(t+3/5)-(d+4/5) by linarith only [steep,cap])
  have weighted : 0≤(t+3/5)*(9/5-(3/2)*d-t) := by
    nlinarith only [chord,en.2.2]
  have last := nonneg_of_mul_nonneg_right weighted
    (show 0<t+3/5 by linarith only [en.1])
  exact ⟨cap,by linarith only [last]⟩

theorem u_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤t) (order : 0≤sigma c s d t) : 0<uPlus c s d t := by
  have eb := normal_bounds en
  have rel := relative_bounds cn en
  have arc := steep_bounds en steep
  let P := (3/2)*d+t-1
  let Q := t-(37/50)*d
  have pl : 0≤P := by dsimp [P]; linarith only [eb.1,steep]
  have pu : P≤4/5 := by dsimp [P]; linarith only [arc.2]
  have ql : 0≤Q := by dsimp [Q]; linarith only [steep,arc.1]
  have qu : Q≤1/5 := by
    have sine := (canonical_bounds en).2.2.2.1
    dsimp [Q]
    linarith only [en.2.1,sine]
  have pw := mul_nonneg (show 0≤kappa c s d t by linarith only [rel.1])
    (show 0≤4/5-P by linarith only [pu])
  have qw := mul_nonneg order (show 0≤1/5-Q by linarith only [qu])
  let z := (4/5)*kappa c s d t+(1/5)*sigma c s d t
  have bound : z^2≤17/25 := by
    have unit := relative_unit cn en
    have square := sq_nonneg (kappa c s d t/5-(4/5)*sigma c s d t)
    dsimp [z]
    nlinarith only [unit,square]
  have small : z<1 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤z-1 by linarith only [bad])
      (show 0≤z+1 by linarith only [bad])
    nlinarith only [product,bound]
  have identity : uPlus c s d t=1-kappa c s d t*P-sigma c s d t*Q := by
    dsimp [uPlus,kappa,sigma,P,Q]
    linear_combination (c+s)*en.2.2
  rw [identity]
  dsimp [z] at small
  nlinarith only [small,pw,qw]

theorem u_negative {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤t) (order : sigma c s d t≤0) : 0<uMinus c s d t := by
  have cb := canonical_bounds cn
  have rel := relative_bounds cn en
  have arc := steep_bounds en steep
  have weight := mul_nonneg (show 0≤kappa c s d t-7/10 by linarith only [rel.1])
    (show 0≤1-d/2 by linarith only [arc.1])
  dsimp [uMinus]
  nlinarith only [weight,cb.2.2.2.2,arc.1,order]

theorem e_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤t) (order : 0≤sigma c s d t) : 0<ePlus c s d t := by
  have cb := canonical_bounds cn
  have rel := relative_bounds cn en
  have arc := steep_bounds en steep
  have coefficient : 0≤1-(3/5)*s := by linarith only [cb.2.2.2.1]
  have weight := mul_nonneg (show 0≤kappa c s d t-7/10 by linarith only [rel.1]) coefficient
  have bracket : 0≤(1+kappa c s d t)*(1-(3/5)*s)-sigma c s d t := by
    nlinarith only [weight,cb.2.2.2.1,rel.2.2.2]
  have product := mul_nonneg order bracket
  have identity : (1+kappa c s d t)*
      (kappa c s d t+sigma c s d t*(1-(3/5)*s)-1)=
      sigma c s d t*((1+kappa c s d t)*(1-(3/5)*s)-sigma c s d t) := by
    linear_combination relative_unit cn en
  have comparison : 1≤kappa c s d t+sigma c s d t*(1-(3/5)*s) := by
    have h := nonneg_of_mul_nonneg_right
      (show 0≤(1+kappa c s d t)*(kappa c s d t+sigma c s d t*(1-(3/5)*s)-1) by
        rw [identity]; exact product)
      (show 0<1+kappa c s d t by linarith only [rel.1])
    linarith only [h]
  have form : ePlus c s d t=1-(3/2)*d-t+
      kappa c s d t+sigma c s d t*(1-(3/5)*s) := by
    dsimp [ePlus,kappa,sigma]
    linear_combination -(d+t)*cn.2.2
  rw [form]
  linarith only [comparison,arc.2]

theorem e_negative {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤t) (order : sigma c s d t≤0) : 0<eMinus c s d t := by
  have cb := canonical_bounds cn
  have rel := relative_bounds cn en
  have arc := steep_bounds en steep
  have weight := mul_nonneg (show 0≤kappa c s d t-7/10 by linarith only [rel.1])
    (show 0≤1-s by linarith only [cb.2.2.2.1])
  have form : eMinus c s d t=1-(3/2)*d+kappa c s d t*(1-s)-sigma c s d t := by
    dsimp [eMinus,kappa,sigma]
    linear_combination -d*cn.2.2
  rw [form]
  nlinarith only [weight,cb.2.2.2.1,arc.1,order]

end
end N12Compact.C1092MPPMPositiveRetainingSteep.Scalars
