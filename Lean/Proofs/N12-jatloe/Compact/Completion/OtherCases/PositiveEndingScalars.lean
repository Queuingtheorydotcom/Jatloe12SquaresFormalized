import Compact.Completion.OtherCases.InwardSignScalars
import Mathlib.Tactic.Positivity

/-! Exact continuous scalar margins for the positive southeast ending.
The two western face bounds use unit-circle identities and one quartic
with positive Bernstein coefficients over its complete half-angle interval. -/
namespace N12Compact.Completion.OtherCases.PositiveEndingScalars
open C1092WallProfileScalars
set_option Elab.async false

private theorem dot_lt (d r x y R : ℝ) (unit : d^2+r^2=1)
    (rp : 0<R) (norm : x^2+y^2<R^2) : d*x+r*y<R := by
  have identity : (d*x+r*y)^2+(d*y-r*x)^2=x^2+y^2 := by
    calc
      _ = (d^2+r^2)*(x^2+y^2) := by ring
      _ = _ := by rw [unit]; ring
  by_contra bad
  have large : R≤d*x+r*y := le_of_not_gt bad
  have product := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤d*x+r*y+R by linarith only [large,rp])
  nlinarith only [identity,norm,product,sq_nonneg (d*y-r*x)]

theorem bar_bounds (c s : ℝ) (cp : 9/10<c) (sp : 0<s)
    (su : s<43/100) (unit : c^2+s^2=1) :
    (c-1)*(c+s)+(13/50)*s^2<0 ∧
      (c-1)*(c-s)+(13/50)*c*s<7/100 := by
  have cu : c≤1 := by nlinarith only [unit,sq_nonneg s,cp]
  have first := mul_pos (sq_pos_of_pos sp)
    (show 0<(c+s)-(13/50)*(1+c) by linarith only [cp,sp])
  have identity : (1+c)*((c-1)*(c+s)+(13/50)*s^2)=
      -s^2*((c+s)-(13/50)*(1+c)) := by
    linear_combination (c+s)*unit
  have negative : (c-1)*(c+s)+(13/50)*s^2<0 := by
    have scaled : (1+c)*((c-1)*(c+s)+(13/50)*s^2)<0 := by
      linarith only [identity,first]
    have positive : 0<(1+c)*(-((c-1)*(c+s)+(13/50)*s^2)) := by
      nlinarith only [scaled]
    have gap := (mul_pos_iff_of_pos_left (show 0<1+c by linarith only [cp])).mp positive
    linarith only [gap]
  have deficit : s^2/2≤1-c := by nlinarith only [unit,sq_nonneg (c-1)]
  have low := mul_nonneg (show 0≤1-c by linarith only [cu])
    (show 0≤c-s-47/100 by linarith only [cp,su])
  have high := mul_nonneg sp.le (show 0≤1-c by linarith only [cu])
  have endpoint := mul_pos (sub_pos.mpr su)
    (show 0<13/50-(47/200)*(43/100+s) by linarith only [su])
  constructor
  · exact negative
  · nlinarith only [low,high,deficit,endpoint]

theorem bar_norm (c s d r : ℝ) (cp : 9/10<c) (sp : 0<s)
    (unit : c^2+s^2=1) (other : d^2+r^2=1) :
    d*((c-1)*(c+s)+(13/50)*s^2)+
      r*((c-1)*(c-s)+(13/50)*c*s)<1-d := by
  let D := (c-1)*(c+s)+(13/50)*s^2
  let R := (c-1)*(c-s)+(13/50)*c*s
  have identity : (1+c)*((1+D)^2+R^2-1)=
      s^2*((6469/2500)-(8531/2500)*c-(63/25)*s) := by
    dsimp only [D,R]
    linear_combination (2*c^3+(13/25)*c^2*s-2*c^2+
      (169/2500)*c*s^2+2*c+(169/2500)*s^2+2*s)*unit
  have negative := mul_neg_of_pos_of_neg (sq_pos_of_pos sp)
    (show (6469/2500)-(8531/2500)*c-(63/25)*s<0 by linarith only [cp,sp])
  have norm : (1+D)^2+R^2<1 := by
    have scaled : (1+c)*((1+D)^2+R^2-1)<0 := by linarith only [identity,negative]
    have positive : 0<(1+c)*(-((1+D)^2+R^2-1)) := by nlinarith only [scaled]
    have gap := (mul_pos_iff_of_pos_left
      (show 0<1+c by linarith only [cp])).mp positive
    linarith only [gap]
  have bound := dot_lt d r (1+D) R 1 other (by norm_num) (by simpa only [one_pow] using norm)
  dsimp only [D,R] at bound
  linarith only [bound]

theorem floor_norm (c s d r : ℝ) (cp : 9/10<c) (sp : 0<s)
    (su : s<1) (unit : c^2+s^2=1) (other : d^2+r^2=1) :
    (1-c)*(s*d+c*r-d)<c*(1-d) := by
  have cu : c<1 := by nlinarith only [unit,sq_pos_of_pos sp,cp]
  have identity : (c-(1-c)*(1-s))^2+(c*(1-c))^2-c^2=
      2*(1-c)*(1-s)*(1-2*c) := by
    linear_combination (c^2-2*c+1)*unit
  have negative := mul_neg_of_pos_of_neg
    (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr cu)) (sub_pos.mpr su))
    (show 1-2*c<0 by linarith only [cp])
  have norm : (c-(1-c)*(1-s))^2+(c*(1-c))^2<c^2 := by
    linarith only [identity,negative]
  have bound := dot_lt d r (c-(1-c)*(1-s)) (c*(1-c)) c other
    (by linarith only [cp]) norm
  nlinarith only [bound]

theorem negative_west_margin (d r : ℝ) (dp : 0<d) (rn : 0≤r)
    (order : r≤d) (unit : d^2+r^2=1) (slope : 7*d<13*r) :
    d-1+(7/20)*r*(d+r)>(1/14)*d := by
  have data := quarter_data d r dp.le rn unit
  let z := half d r
  have zn : 0≤z := data.1
  have zu : z<5/12 := by
    have relation : 2*z≤1-z^2 := by nlinarith only [data.2.2.2.1,data.2.2.2.2,
      (mul_nonneg (show 0≤1+z^2 by positivity) (sub_nonneg.mpr order))]
    by_contra bad
    have high : 5/12≤z := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤z+5/12 by linarith only [zn])
    nlinarith only [relation,square,high]
  have zl : 1/4<z := by
    have relation := mul_pos (show 0<1+z^2 by positivity) (sub_pos.mpr slope)
    have projection : 0<26*z-7*(1-z^2) := by
      nlinarith only [relation,data.2.2.2.1,data.2.2.2.2]
    by_contra bad
    have low : z≤1/4 := le_of_not_gt bad
    have square := mul_nonneg zn (sub_nonneg.mpr low)
    nlinarith only [projection,square,low]
  have certificate :
      -1/14+(7/10)*z-(3/5)*z^2-(7/10)*z^3-(27/14)*z^4 =
      (69093/1120)*(5/12-z)^4+
      (11151/40)*(z-1/4)*(5/12-z)^3+
      (223803/560)*(z-1/4)^2*(5/12-z)^2+
      (54309/280)*(z-1/4)^3*(5/12-z)+
      (303/32)*(z-1/4)^4 := by ring
  have lower : 0<z-1/4 := sub_pos.mpr zl
  have upper : 0<5/12-z := sub_pos.mpr zu
  have positive : 0< -1/14+(7/10)*z-(3/5)*z^2-(7/10)*z^3-(27/14)*z^4 := by
    rw [certificate]
    positivity
  have identity : (1+z^2)^2*((13/14)*d-1+(7/20)*r*(d+r))=
      -1/14+(7/10)*z-(3/5)*z^2-(7/10)*z^3-(27/14)*z^4 := by
    calc
      _ = (13/14)*(1+z^2)*((1+z^2)*d)-(1+z^2)^2+
          (7/20)*((1+z^2)*r)*((1+z^2)*d+(1+z^2)*r) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  have scaled : 0<(1+z^2)^2*((13/14)*d-1+(7/20)*r*(d+r)) := by
    rwa [identity]
  have good := (mul_pos_iff_of_pos_left (sq_pos_of_pos
    (show 0<1+z^2 by positivity))).mp scaled
  linarith only [good]

private theorem large_sum (d r : ℝ) (dp : 0<d) (rn : 13/20≤r)
    (order : r≤d) (unit : d^2+r^2=1) : 176/125<d+r := by
  have difference := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤d+r by linarith only [dp,rn])
  have ru : r≤5/7 := by
    by_contra bad
    have high : 5/7<r := lt_of_not_ge bad
    have square := mul_pos (sub_pos.mpr high)
      (show 0<r+5/7 by linarith only [high])
    nlinarith only [difference,unit,square]
  by_contra bad
  have sum : d+r≤176/125 := le_of_not_gt bad
  have square := mul_nonneg (show 0≤176/125-r-d by linarith only [sum])
    (show 0≤176/125-r+d by linarith only [sum,dp])
  have interval := mul_nonneg (show 0≤r-13/20 by linarith only [rn])
    (show 0≤379/500-r by linarith only [ru])
  nlinarith only [unit,square,interval]

theorem positive_west_margin (d r : ℝ) (dp : 0<d) (rn : 0≤r)
    (order : r≤d) (unit : d^2+r^2=1) :
    (7/200<(7/20)*(d-r) ∨
        7/200<(7/20)*(d-r)+1-(13/20)/r) ∧
    ((12/113)*(1-r)<(7/20)*(d-r) ∨
        (12/113)*(1-r)<(7/20)*(d-r)+1-(13/20)/r) := by
  by_cases small : r≤13/20
  · have dl : 759/1000<d := by
      by_contra bad
      have low : d≤759/1000 := le_of_not_gt bad
      have ds := mul_nonneg (sub_nonneg.mpr low)
        (show 0≤759/1000+d by linarith only [dp])
      have rs := mul_nonneg (sub_nonneg.mpr small)
        (show 0≤13/20+r by linarith only [rn])
      nlinarith only [unit,ds,rs]
    exact ⟨Or.inl (by linarith only [dl,small]),Or.inl (by linarith only [dl,small])⟩
  · have rp : 0<r := by linarith only [small]
    have bounds := CommonCases.CanonicalScalars.bounds d r dp rn order unit
    have ru : r≤5/7 := by
      have difference := mul_nonneg (sub_nonneg.mpr order) (add_nonneg dp.le rn)
      by_contra bad
      have high : 5/7<r := lt_of_not_ge bad
      have square := mul_pos (sub_pos.mpr high)
        (show 0<r+5/7 by linarith only [rp])
      nlinarith only [unit,difference,square]
    have sum := large_sum d r dp (by linarith only [small]) order unit
    have interval := mul_nonneg (show 0≤r-13/20 by linarith only [small])
      (show 0≤5/7-r by linarith only [ru])
    have weight := mul_pos rp (show 0<d+r-176/125 by linarith only [sum])
    have first : r*(7/200)<r*((7/20)*(d-r)+1)-(13/20) := by
      nlinarith only [interval,weight,small,ru]
    have second : r*((12/113)*(1-r))<r*((7/20)*(d-r)+1)-(13/20) := by
      nlinarith only [interval,weight,small,ru]
    have cancel : r*((13/20)/r)=13/20 := by
      rw [mul_comm,div_mul_cancel₀ _ rp.ne']
    have exactFirst : 7/200<(7/20)*(d-r)+1-(13/20)/r := by
      apply (mul_lt_mul_iff_right₀ rp).mp
      simpa only [mul_sub,cancel] using first
    have exactSecond : (12/113)*(1-r)<(7/20)*(d-r)+1-(13/20)/r := by
      apply (mul_lt_mul_iff_right₀ rp).mp
      simpa only [mul_sub,cancel] using second
    exact ⟨Or.inr exactFirst,Or.inr exactSecond⟩

#print axioms bar_norm
#print axioms floor_norm
#print axioms negative_west_margin
#print axioms positive_west_margin
end N12Compact.Completion.OtherCases.PositiveEndingScalars
