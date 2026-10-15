import Compact.Completion.C1092.MPPMNegativeCrosspointCoefficients
import Compact.Completion.C1092.MPPMNegativeCrosspointG10High

/-! NEGATIVE-WALL-SCALARS §6 on its exact required domain h<=r.
The lower successor piece is affine on the doubled-angle unit circle,
so one circle chord replaces the concavity argument. The upper piece
uses the already proved finite coefficient order and the same aligned
G10 value. No division by the successor sine or endpoint omission occurs. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

private theorem radial {h r : ℝ} (q : Quarter h r) (order : h≤r) :
    0<r ∧ 0≤h/r ∧ h/r≤1 ∧ h=(h/r)*r ∧
      (1+(h/r)^2)*r^2=1 ∧ r^2*(1+h/r)*(1+(2/5)*(h/r)^2)≤h+r := by
  have rp : 0<r := by
    apply lt_of_not_ge
    intro bad
    have rzero : r=0 := by linarith only [bad,q.sine]
    have hzero : h=0 := by linarith only [order,q.cosine,rzero]
    nlinarith only [q.unit,rzero,hzero]
  let u := h/r
  have un : 0≤u := div_nonneg q.cosine rp.le
  have uh : u≤1 := (div_le_iff₀ rp).mpr (by simpa using order)
  have hu : h=u*r := (div_mul_cancel₀ _ rp.ne').symm
  have unit : (1+u^2)*r^2=1 := by
    have circle := q.unit
    rw [hu] at circle
    nlinarith only [circle]
  have square := mul_nonneg (show 0≤1-u by linarith only [uh])
    (show 0≤1+u by linarith only [un])
  have remainder := mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg u))
    (show 0≤1/5-(4/25)*u^2 by nlinarith only [square])
  have identity : 1-(r*(1+(2/5)*u^2))^2=
      r^2*u^2*(1/5-(4/25)*u^2) := by linear_combination -unit
  have chord : r*(1+(2/5)*u^2)≤1 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<r*(1+(2/5)*u^2)-1 by linarith only [bad])
      (show 0<r*(1+(2/5)*u^2)+1 by positivity)
    nlinarith only [identity,remainder,product]
  have weight := mul_le_mul_of_nonneg_left chord (show 0≤r*(1+u) by positivity)
  have lower : r^2*(1+u)*(1+(2/5)*u^2)≤h+r := by nlinarith only [weight,hu]
  exact ⟨rp,un,uh,hu,unit,lower⟩

private theorem zero_model (c s h r : ℝ) (cn : Normal c s)
    (q : Quarter h r) (order : h≤r) : 0≤h+r-2-h*FC c s h r+r^2 := by
  have data := radial q order
  let u := h/r
  have un : 0≤u := data.2.1
  have uh : u≤1 := data.2.2.1
  have hu : h=u*r := data.2.2.2.1
  have unit : (1+u^2)*r^2=1 := data.2.2.2.2.1
  have chord : r^2*(1+u)*(1+(2/5)*u^2)≤h+r := data.2.2.2.2.2
  have cap := FC_high_cap c s h r cn q order
  have weight := mul_le_mul_of_nonneg_left cap q.cosine
  have product := mul_nonneg (show 0≤1-u by linarith only [uh])
    (show 0≤11/10-(2/5)*(1+u) by linarith only [uh])
  have bracket : 0≤91/100-(11/10)*u+(2/5)*u^2 := by nlinarith only [product]
  have positive := mul_nonneg (sq_nonneg r) (mul_nonneg un bracket)
  have identity : h+r-2+h^2/2-(9/100)*h*r+r^2=
      r^2*u*(91/100-(11/10)*u+(2/5)*u^2)+
      (h+r-r^2*(1+u)*(1+(2/5)*u^2)) := by
    rw [hu]
    linear_combination 2*unit
  nlinarith only [weight,positive,identity,chord]

private theorem slope_model (c s h r : ℝ) (cn : Normal c s)
    (q : Quarter h r) (order : h≤r) (slope : 3*r≤8*h) :
    0≤h+r-2-h*FC c s h r+(771/3650)*h*r+(601/730)*r^2 := by
  have data := radial q order
  let u := h/r
  have un : 0≤u := data.2.1
  have hu : h=u*r := data.2.2.2.1
  have unit : (1+u^2)*r^2=1 := data.2.2.2.2.1
  have chord : r^2*(1+u)*(1+(2/5)*u^2)≤h+r := data.2.2.2.2.2
  have ul : 3/8≤u := by
    apply (le_div_iff₀ data.1).mpr
    linarith only [slope]
  have bracket : 0≤(2/5)*u^2-(19/20)*u+611/800 := by
    nlinarith only [sq_nonneg (u-19/16)]
  have product := mul_nonneg (show 0≤u-3/8 by linarith only [ul]) bracket
  have polynomial : 0≤-9/50+(28/25)*u-(11/10)*u^2+(2/5)*u^3 := by
    have identity : -9/50+(28/25)*u-(11/10)*u^2+(2/5)*u^3=
        681/6400+(u-3/8)*((2/5)*u^2-(19/20)*u+611/800) := by ring
    nlinarith only [identity,product]
  have positive := mul_nonneg (sq_nonneg r) polynomial
  have cap := FC_high_cap c s h r cn q order
  have weight := mul_le_mul_of_nonneg_left cap q.cosine
  have identity : h+r-2+h^2/2+(3/25)*h*r+(41/50)*r^2=
      r^2*(-9/50+(28/25)*u-(11/10)*u^2+(2/5)*u^3)+
      (h+r-r^2*(1+u)*(1+(2/5)*u^2)) := by
    rw [hu]
    linear_combination 2*unit
  nlinarith only [weight,positive,identity,chord,mul_nonneg q.cosine q.sine,sq_nonneg r]

private def doubleC (d t : ℝ) : ℝ := d^2-t^2
private def doubleS (d t : ℝ) : ℝ := 2*d*t

private theorem double_quarter {d t : ℝ} (en : Normal d t) :
    Quarter (doubleC d t) (doubleS d t) := by
  have eb := normal_bounds en
  have product := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t by linarith only [eb.1,en.1])
  refine ⟨by dsimp [doubleC]; nlinarith only [product],
    by
      dsimp [doubleS]
      exact mul_nonneg (mul_nonneg (by norm_num) (by linarith only [eb.1])) en.1,?_⟩
  dsimp [doubleC,doubleS]
  linear_combination (d^2+t^2+1)*en.2.2

private theorem double_order {d t D T : ℝ} (en : Normal d t) (last : Normal D T)
    (order : t≤T) : doubleS d t≤doubleS D T := by
  have eq := double_quarter en
  have lq := double_quarter last
  have product := mul_nonneg (sub_nonneg.mpr order) (add_nonneg en.1 last.1)
  have cosine : doubleC D T≤doubleC d t := by
    dsimp [doubleC]
    nlinarith only [product,en.2.2,last.2.2]
  exact CommonCases.UnitCircleChord.cosine_order lq.sine eq.sine
    (by nlinarith only [lq.unit]) (by nlinarith only [eq.unit]) lq.cosine eq.cosine cosine

private def A (h r : ℝ) : ℝ := (13/100)*h*r+(37/100)*r^2
private def B (h r : ℝ) : ℝ := (37/100)*h*r-(13/100)*r^2
private def base (c s h r : ℝ) : ℝ := h+r-2-h*FC c s h r+r^2-A h r

private theorem before_form (c s d t h r : ℝ) (en : Normal d t)
    (branch : deltaE d t h r≤0) :
    G11 c s d t h r=base c s h r+A h r*doubleC d t+B h r*doubleS d t := by
  rw [G11,FE_lower_formula d t h r en branch]
  dsimp [base,A,B,doubleC,doubleS,P,Q]
  linear_combination -((13/100)*h*r+(37/100)*r^2)*en.2.2

private theorem aligned (c s h r : ℝ) (q : Quarter h r) (rn : Normal r h) :
    G11 c s r h h r=G10 c s r h h r := by
  have zero : deltaE r h h r=0 := by dsimp [deltaE]; ring
  have self : kE r h h r=1 := by dsimp [kE]; nlinarith only [q.unit]
  dsimp only [G11,G10]
  rw [FE_aligned r h rn,zero,self,abs_zero]
  ring

private theorem before (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (shallow : 8*t≤3*d) (q : Quarter h r) (order : h≤r)
    (branch : deltaE d t h r≤0) : 0≤G11 c s d t h r := by
  have rn : Normal r h := ⟨q.cosine,order,by nlinarith only [q.unit]⟩
  have eq := double_quarter en
  have aq : 0≤A h r := by
    dsimp [A]
    nlinarith only [mul_nonneg q.cosine q.sine,sq_nonneg r]
  have first : 0≤base c s h r+A h r*1+B h r*0 := by
    have endpoint := zero_model c s h r cn q order
    dsimp [base]
    nlinarith only [endpoint]
  by_cases small : 8*h≤3*r
  · have sine : t≤h := sine_order rn en (by dsimp [deltaE] at branch; nlinarith only [branch])
    have uq := double_quarter rn
    have endpoint := G10_nonnegative c s r h h r cn steep rn small q
    rw [←aligned c s h r q rn] at endpoint
    rw [before_form c s r h h r rn (by dsimp [deltaE]; nlinarith)] at endpoint
    have result := CommonCases.UnitCircleChord.linear_nonnegative
      (c:=1) (s:=0) (d:=doubleC r h) (t:=doubleS r h)
      (h:=doubleC d t) (r:=doubleS d t) (b:=base c s h r) (A:=A h r) (B:=B h r)
      (by norm_num) uq.cosine eq.cosine (by norm_num) uq.unit eq.unit
      eq.sine (double_order en rn sine) aq first endpoint
    rw [before_form c s d t h r en branch]
    exact result
  · have upper : doubleS d t≤48/73 := by
      have eb := normal_bounds en
      have product := mul_nonneg (show 0≤3*d-8*t by linarith only [shallow])
        (show 0≤8*d-3*t by linarith only [en.2.1,eb.1])
      dsimp [doubleS]
      nlinarith only [product,en.2.2]
    have endpoint : 0≤base c s h r+A h r*(55/73)+B h r*(48/73) := by
      have value := slope_model c s h r cn q order (lt_of_not_ge small).le
      dsimp [base,A,B]
      nlinarith only [value]
    have result := CommonCases.UnitCircleChord.linear_nonnegative
      (c:=1) (s:=0) (d:=55/73) (t:=48/73)
      (h:=doubleC d t) (r:=doubleS d t) (b:=base c s h r) (A:=A h r) (B:=B h r)
      (by norm_num) (by norm_num) eq.cosine (by norm_num) (by norm_num) eq.unit
      eq.sine upper aq first endpoint
    rw [before_form c s d t h r en branch]
    exact result

private theorem after (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (shallow : 8*t≤3*d) (q : Quarter h r) (order : h≤r)
    (branch : 0≤deltaE d t h r) : 0≤G11 c s d t h r := by
  have rn : Normal r h := ⟨q.cosine,order,by nlinarith only [q.unit]⟩
  have sine : h≤t := sine_order en rn (by dsimp [deltaE] at branch; nlinarith only [branch])
  have cosine : d≤r := cosine_order en rn sine
  have small : 8*h≤3*r := by linarith only [sine,shallow,cosine]
  have coefficients := second_order en rn shallow small sine
  have first := mul_le_mul_of_nonneg_right coefficients.1 q.cosine
  have last := mul_le_mul_of_nonneg_right coefficients.2 q.sine
  have compare : FE d t h r≤FE r h h r := by
    rw [FE_upper_formula d t h r branch,
      FE_upper_formula r h h r (by dsimp [deltaE]; nlinarith)]
    linarith only [first,last]
  have weight := mul_le_mul_of_nonneg_left compare q.sine
  have endpoint := G10_nonnegative c s r h h r cn steep rn small q
  rw [←aligned c s h r q rn] at endpoint
  dsimp [G11] at endpoint ⊢
  linarith only [weight,endpoint]

/-- Exactly the upper half-quadrant required by the actual negative
successor application. The lower half is excluded by its strict anchors. -/
theorem G11_nonnegative (c s d t h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (en : Normal d t) (shallow : 8*t≤3*d) (q : Quarter h r) (order : h≤r) :
    0≤G11 c s d t h r := by
  by_cases branch : 0≤deltaE d t h r
  · exact after c s d t h r cn steep en shallow q order branch
  · exact before c s d t h r cn steep en shallow q order (lt_of_not_ge branch).le

end
end N12Compact.C1092MPPMNegativeCrosspointSupport
