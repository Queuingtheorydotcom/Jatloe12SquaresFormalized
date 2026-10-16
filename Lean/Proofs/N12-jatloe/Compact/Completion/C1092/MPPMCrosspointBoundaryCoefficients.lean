import Compact.Completion.C1092.MPPMCrosspointSupportScalars
import Mathlib.Data.Real.Sqrt

/-! STEEP-POSITIVE-BOUNDARY-SCALARS §2. Exact finite differences replace
the two derivative arguments. Every bound includes both canonical endpoints. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def P (d t : ℝ) : ℝ := 1-d-(3/5)*t^2+(11/25)*d*t
def Q (d t : ℝ) : ℝ := 1+t-(11/25)*t^2-(3/5)*d*t

theorem FE_after {d t h r : ℝ} (en : Normal d t)
    (order : 0≤deltaE d t h r) : FE d t h r=P d t*h-Q d t*r := by
  rw [FE,if_pos order]
  dsimp [kE,deltaE,E0,P,Q]
  linear_combination (h-r)*en.2.2

theorem coefficient_order {d t d₀ t₀ : ℝ}
    (en : Normal d t) (base : Normal d₀ t₀) (order : t₀≤t) :
    P d₀ t₀≤P d t ∧ Q d₀ t₀≤Q d t := by
  have eb := normal_bounds en
  have bb := normal_bounds base
  let D := d+d₀
  let T := t+t₀
  have Dlo : 7/5≤D := by dsimp [D]; linarith only [eb.1,bb.1]
  have Dhi : D≤2 := by dsimp [D]; linarith only [eb.2.1,bb.2.1]
  have Tn : 0≤T := add_nonneg en.1 base.1
  have TD : T≤D := by dsimp [T,D]; linarith only [en.2.1,base.2.1]
  have Thi : T≤10/7 := by
    have es := mul_nonneg (sub_nonneg.mpr en.2.1)
      (show 0≤d+t by linarith only [eb.1,en.1])
    have bs := mul_nonneg (sub_nonneg.mpr base.2.1)
      (show 0≤d₀+t₀ by linarith only [bb.1,base.1])
    have te : t≤5/7 := by nlinarith only [en.2.2,es,en.1,sq_nonneg (t-5/7)]
    have tb : t₀≤5/7 := by nlinarith only [base.2.2,bs,base.1,sq_nonneg (t₀-5/7)]
    dsimp [T]; linarith only [te,tb]
  have circle : D^2+T^2≤4 := by
    dsimp [D,T]
    nlinarith only [en.2.2,base.2.2,sq_nonneg (d-d₀),sq_nonneg (t-t₀)]
  have difference : 0≤D^2-T^2 := by
    have product := mul_nonneg (sub_nonneg.mpr TD)
      (show 0≤D+T by linarith only [Dlo,Tn])
    nlinarith only [product]
  have pbracket : 0≤T*(1-(3/5)*D)+(11/50)*(D^2-T^2) := by
    by_cases low : D≤5/3
    · have product := mul_nonneg Tn (show 0≤1-(3/5)*D by linarith only [low])
      nlinarith only [product,difference]
    · have high : 5/3≤D := (lt_of_not_ge low).le
      have square := mul_nonneg (show 0≤D-5/3 by linarith only [high])
        (show 0≤D+5/3 by linarith only [Dlo])
      have Tsmall : T≤28/25 := by
        nlinarith only [circle,square,Tn,sq_nonneg (T-28/25)]
      have first := mul_nonneg Tn (show 0≤(3/5)*(2-D) by linarith only [Dhi])
      nlinarith only [first,circle,square,Tsmall]
  have qbracket : 0≤D*(1-(11/25)*T)-(3/10)*D^2+(3/10)*T^2 := by
    have product := mul_nonneg (show 0≤D-7/5 by linarith only [Dlo])
      (show 0≤1-(11/25)*T by linarith only [Thi])
    nlinarith only [product,circle,sq_nonneg (T-77/150)]
  have pi : D*(P d t-P d₀ t₀)=
      (t-t₀)*(T*(1-(3/5)*D)+(11/50)*(D^2-T^2)) := by
    dsimp [P,D,T]
    linear_combination (1-(11/50)*(t+t₀))*base.2.2-
      (1-(11/50)*(t+t₀))*en.2.2
  have qi : D*(Q d t-Q d₀ t₀)=
      (t-t₀)*(D*(1-(11/25)*T)-(3/10)*D^2+(3/10)*T^2) := by
    dsimp [Q,D,T]
    linear_combination ((3/10)*(t+t₀))*base.2.2-
      ((3/10)*(t+t₀))*en.2.2
  have pp := mul_nonneg (sub_nonneg.mpr order) pbracket
  have qp := mul_nonneg (sub_nonneg.mpr order) qbracket
  rw [←pi] at pp
  rw [←qi] at qp
  have dp : 0<D := by linarith only [Dlo]
  have pr := nonneg_of_mul_nonneg_right pp dp
  have qr := nonneg_of_mul_nonneg_right qp dp
  exact ⟨by linarith only [pr],by linarith only [qr]⟩

theorem coefficient_bounds {d t : ℝ} (en : Normal d t) :
    0≤P d t ∧ P d t<213/1000 ∧ 1≤Q d t ∧ Q d t<297/250 ∧
      203/250<2-Q d t ∧ 2-Q d t≤1 ∧ P d t+2-Q d t<111/100 := by
  have eb := normal_bounds en
  let v := Real.sqrt 2/2
  have vp : 0<v := by dsimp [v]; positivity
  have vs : v^2=1/2 := by
    dsimp [v]
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have vlo : 707/1000<v := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (sub_nonneg.mpr bad)
      (show 0≤707/1000+v by linarith only [vp])
    nlinarith only [product,vs]
  have vhi : v<177/250 := by nlinarith only [vs,vp,sq_nonneg (v-177/250)]
  have vn : Normal v v := ⟨vp.le,le_rfl,by linarith only [vs]⟩
  have tv : t≤v := by
    have product := mul_nonneg (sub_nonneg.mpr en.2.1)
      (show 0≤d+t by linarith only [eb.1,en.1])
    apply le_of_not_gt
    intro bad
    have strict := mul_pos (sub_pos.mpr bad)
      (show 0<t+v by linarith only [vp,bad])
    nlinarith only [strict,product,en.2.2,vs]
  have low := coefficient_order en (show Normal 1 0 by norm_num [Normal]) en.1
  have high := coefficient_order vn en tv
  have pl : 0≤P d t := by simpa [P] using low.1
  have ql : 1≤Q d t := by simpa [Q] using low.2
  have pv : P v v=23/25-v := by dsimp [P]; nlinarith only [vs]
  have qv : Q v v=12/25+v := by dsimp [Q]; nlinarith only [vs]
  have ph : P d t<213/1000 := by linarith only [high.1,pv,vlo]
  have qh : Q d t<297/250 := by linarith only [high.2,qv,vhi]
  have sumhi : d+t≤283/200 := by
    nlinarith only [en.2.2,sq_nonneg (d-t),sq_nonneg (d+t-283/200)]
  have product := mul_nonneg (show 0≤283/200-(d+t) by linarith only [sumhi])
    (show 0≤(13/25)*(283/200+(d+t))-1 by linarith only [eb.2.2.2.2.1])
  have sum_identity : P d t+2-Q d t=
      37/25-(d+t)+(13/25)*(d+t)^2-(4/25)*t^2 := by
    dsimp [P,Q]
    linear_combination -(13/25)*en.2.2
  have sum : P d t+2-Q d t<111/100 := by
    nlinarith only [sum_identity,product,sq_nonneg t]
  exact ⟨pl,ph,ql,qh,by linarith only [qh],by linarith only [ql],sum⟩

theorem coefficient_difference {d t : ℝ} (en : Normal d t) :
    89/100≤Q d t-P d t := by
  have eb := normal_bounds en
  have upper : d+t≤283/200 := by
    nlinarith only [en.2.2,sq_nonneg (d-t),sq_nonneg (d+t-283/200)]
  have chord := mul_nonneg (show 0≤d+t-1 by linarith only [eb.2.2.2.2.1])
    (show 0≤283/200-(d+t) by linarith only [upper])
  have identity : Q d t-P d t=
      d+t-(13/25)*(d+t)^2+13/25+(4/25)*t^2 := by
    dsimp [P,Q]
    linear_combination (13/25)*en.2.2
  nlinarith only [identity,chord,upper,sq_nonneg t]

end
end N12Compact.C1092MPPMCrosspointSupport
