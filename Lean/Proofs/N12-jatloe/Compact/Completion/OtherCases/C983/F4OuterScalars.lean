import Compact.Completion.C981.SupportForms

/-! The whole-interval estimates in C983-F4-TOP-ONLY-8208-ENDING §4 and
C983-F4-MIXED-NEGATIVE-8208-ENDING §4. Decimal constants in those chapters
are written as exact rationals. The circle chord below is the algebraic
form of the manuscript's concavity argument, not a sampled angle test. -/
namespace N12Compact.Completion.OtherCases.C983.F4OuterScalars
set_option Elab.async false

theorem outer_cap (c s : ℝ) (cp : 19/20<c) (sp : 0<s) (ss : s<3/10)
    (unit : c^2+s^2=1) (half : s/(1+c)<3/20) : c+s/2-1<42/409 := by
  have cn : 0<c := by linarith only [cp]
  have hp : 0<1+c := by linarith only [cn]
  have angle : 20*s<3*(1+c) := by
    have h := (div_lt_iff₀ hp).mp half
    linarith only [h]
  have sb : s<120/409 := by
    apply lt_of_not_ge
    intro bad
    have positive : 0<3*c+(20*s-3) := by linarith only [cn,bad]
    have product := mul_pos (show 0<3*c-(20*s-3) by linarith only [angle]) positive
    have obstruction := mul_nonneg sp.le (show 0≤409*s-120 by linarith only [bad])
    nlinarith only [unit,product,obstruction]
  have diff := mul_pos (sub_pos.mpr sb)
    (show 0<(c+391/409)/2-(s+120/409) by linarith only [cp,ss])
  have identity :
      ((451/409)-(c+s/2))*(c+391/409)=
        (120/409-s)*((c+391/409)/2-(s+120/409)) := by
    nlinarith only [unit]
  have positive : 0<c+391/409 := by linarith only [cn]
  have result : 0<(451/409)-(c+s/2) := by
    apply lt_of_not_ge
    intro bad
    have impossible := mul_nonpos_of_nonpos_of_nonneg bad positive.le
    linarith only [impossible,identity,diff]
  linarith only [result]

private theorem cosine_quadratic (d r : ℝ) (_dp : 0<d)
    (unit : d^2+r^2=1) : d≤1-r^2/2 := by
  nlinarith only [unit,sq_nonneg (d-1)]

theorem positive_angle (d r : ℝ) (dp : 0<d) (rn : 0≤r)
    (unit : d^2+r^2=1) (width : 1<r+(19/25)*d) : 13/50<r := by
  have quadratic := cosine_quadratic d r dp unit
  apply lt_of_not_ge
  intro bad
  have product := mul_nonneg (show 0≤13/50-r by linarith only [bad])
    (show 0≤1-(19/50)*(r+13/50) by linarith only [bad,rn])
  nlinarith only [width,quadratic,product]

private theorem cubic_floor (r : ℝ) (lo : 13/50≤r) (hi : r≤3/5) :
    1401/12500≤(37/50)*r-r^2+(13/100)*r^3 := by
  have increasing := mul_nonneg (sub_nonneg.mpr lo)
    (show 0≤461/500-(13/100)*(r+13/50) by linarith only [hi])
  have factor : 0≤(461/500)*r-467/2500-(13/100)*r^2 := by
    nlinarith only [increasing]
  have product := mul_nonneg (show 0≤3/5-r by linarith only [hi]) factor
  nlinarith only [product]

private theorem product_floor (d r : ℝ) (dp : 0<d) (lo : 3/5≤r)
    (order : r≤d) (unit : d^2+r^2=1) : 12/25≤d*r := by
  have rp : 0<r := by linarith only [lo]
  have r2lo : 9/25≤r^2 := by nlinarith only [lo]
  have r2hi : r^2≤1/2 := by nlinarith only [unit,order,dp,rp]
  have product := mul_nonneg (show 0≤r^2-9/25 by linarith only [r2lo])
    (show 0≤16/25-r^2 by linarith only [r2hi])
  have circle : (d*r)^2=r^2-r^4 := by
    linear_combination r^2*unit
  have square : (12/25)^2≤(d*r)^2 := by
    nlinarith only [product,circle]
  nlinarith only [square,mul_pos dp rp]

/-- The two positive-W support intervals, with the larger mixed-branch cap. -/
theorem positive_support (c s d r A V : ℝ)
    (cp : 19/20<c) (sp : 0<s) (ss : s<3/10) (eu : c^2+s^2=1)
    (dp : 0<d) (rn : 0≤r) (order : r≤d) (wu : d^2+r^2=1)
    (angle : 13/50<r) (ap : 0<A)
    (first : (13/50)*d< -V) (last : 1-r-(13/50)*d< -V) :
    42/409<(c*d-s*r)*A-(c*r+s*d)*V := by
  have cn : 0<c := by linarith only [cp]
  have rp : 0<r := by linarith only [angle]
  have kp : 0<c*d-s*r := by
    have bound := mul_nonneg sp.le (sub_nonneg.mpr order)
    have gap := mul_pos dp (show 0<c-s by linarith only [cp,ss])
    nlinarith only [bound,gap]
  have hp : 0<c*r+s*d := by positivity
  have firstTerm := mul_pos kp ap
  by_cases small : r≤3/5
  · have quadratic := cosine_quadratic d r dp wu
    let f := 37/50-r+(13/100)*r^2
    have fp : 0<f := by dsimp only [f]; nlinarith only [small,sq_nonneg r]
    have face : f< -V := by dsimp only [f]; linarith only [quadratic,last]
    have lower := mul_pos hp (sub_pos.mpr face)
    have hbound : (19/20)*r<c*r+s*d := by
      have h := mul_pos (sub_pos.mpr cp) rp
      have t := mul_pos sp dp
      nlinarith only [h,t]
    have extra := mul_pos fp (sub_pos.mpr hbound)
    have floor := cubic_floor r angle.le small
    dsimp only [f] at lower extra
    nlinarith only [firstTerm,lower,extra,floor]
  · have product := product_floor d r dp (le_of_not_ge small) order wu
    have lower := mul_pos hp (sub_pos.mpr first)
    have extra := mul_pos sp (sq_pos_of_pos dp)
    have cBound := mul_pos (sub_pos.mpr cp) (mul_pos dp rp)
    nlinarith only [firstTerm,lower,extra,cBound,product]

/-- The algebraic chord under r*sqrt(1-r²) on [.39,1/sqrt(2)]. -/
private theorem negative_chord (d r : ℝ) (dp : 0<d) (lo : 39/100<r)
    (order : r≤d) (unit : d^2+r^2=1) :
    (1-(1412/3479))/2+(1412/3479)*r^2≤d*r := by
  let k : ℝ := 1412/3479
  let u := r^2
  let L := (1-k)/2+k*u
  have rp : 0<r := by linarith only [lo]
  have ulo : 1521/10000≤u := by dsimp only [u]; nlinarith only [lo]
  have uhi : u≤1/2 := by dsimp only [u]; nlinarith only [order,dp,rp,unit]
  have ln : 0≤L := by dsimp only [L,k]; positivity
  have factor : 0≤(1+k^2)*u-(1-k)^2/2 := by
    dsimp only [k]
    nlinarith only [ulo]
  have product := mul_nonneg (show 0≤1/2-u by linarith only [uhi]) factor
  have identity : u-u^2-L^2=(1/2-u)*((1+k^2)*u-(1-k)^2/2) := by
    dsimp only [L]
    ring
  have square : L^2≤(d*r)^2 := by
    have circle : (d*r)^2=u-u^2 := by
      dsimp only [u]
      linear_combination r^2*unit
    linarith only [product,identity,circle]
  have result : L≤d*r := by nlinarith only [square,ln,mul_pos dp rp]
  simpa only [L,k,u] using result

/-- The manuscript's concave endpoint bound (49)--(51). -/
theorem negative_support (c s d r : ℝ)
    (cp : 19/20<c) (sp : 0<s) (ss : s<3/10) (eu : c^2+s^2=1)
    (dp : 0<d) (lo : 39/100<r) (order : r≤d) (wu : d^2+r^2=1) :
    42/409<c*((61/100)*d*r-(7/20)*r^2)+
      s*((61/100)*r^2+(7/20)*d*r-7/20) := by
  let k : ℝ := 1412/3479
  let A := ((61/100)*c+(7/20)*s)*(1-k)/2-(7/20)*s
  let B := ((61/100)*c+(7/20)*s)*k-(7/20)*c+(61/100)*s
  have cn : 0<c := by linarith only [cp]
  have rp : 0<r := by linarith only [lo]
  have low : 1521/10000≤r^2 := by nlinarith only [lo]
  have high : r^2≤1/2 := by nlinarith only [order,dp,rp,wu]
  have chord := negative_chord d r dp lo order wu
  have weight := mul_nonneg (show 0≤(61/100)*c+(7/20)*s by positivity)
    (sub_nonneg.mpr chord)
  have compare : A+B*r^2≤c*((61/100)*d*r-(7/20)*r^2)+
      s*((61/100)*r^2+(7/20)*d*r-7/20) := by
    dsimp only [A,B,k]
    nlinarith only [weight]
  have endpointLow : 2343/20000<A+B*(1521/10000) := by
    dsimp only [A,B,k]
    nlinarith only [cp,sp,ss]
  have sum : 1≤c+s := by nlinarith only [eu,mul_nonneg cn.le sp.le,cn,sp]
  have endpointHigh : 13/100≤A+B*(1/2) := by
    dsimp only [A,B,k]
    nlinarith only [sum]
  by_cases bn : 0≤B
  · have monotone := mul_nonneg bn (sub_nonneg.mpr low)
    nlinarith only [compare,endpointLow,monotone]
  · have monotone := mul_nonneg (neg_nonneg.mpr (le_of_not_ge bn))
      (sub_nonneg.mpr high)
    nlinarith only [compare,endpointHigh,monotone]

/-- Replacement estimate (11)--(13), retaining the exact missing-S face
instead of weakening it to the numerical cap. -/
theorem negative_own_support (c s d r : ℝ)
    (cp : 19/20<c) (sp : 0<s) (ss : s<3/10) (eu : c^2+s^2=1)
    (dp : 0<d) (lo : 39/100<r) (wu : d^2+r^2=1) :
    (c*d+s*r)*(c+s/2-1)-(c*r-s*d)*(s/2)<(13/50)*r := by
  have cn : 0<c := by linarith only [cp]
  have cu : c≤1 := by nlinarith only [eu,sq_nonneg s,cn]
  have du : d<921/1000 := by nlinarith only [wu,lo,dp]
  let A := (c-1)^2/2+c*s/2
  let B := s^2/2-s+c*s/2-13/50
  have an : 0≤A := by dsimp only [A]; positivity
  have gapSquare : (c-1)^2<1/400 := by nlinarith only [cp,cu]
  have cs := mul_nonneg sp.le (sub_nonneg.mpr cu)
  have ab : A<1/800+s/2 := by dsimp only [A]; nlinarith only [gapSquare,cs]
  have bb : B≤s^2/2-s/2-13/50 := by dsimp only [B]; nlinarith only [cs]
  have bn : B<0 := by dsimp only [B]; nlinarith only [ss,sp,cs]
  have first := mul_nonneg an (sub_nonneg.mpr du.le)
  have second := mul_pos (sub_pos.mpr ab) (show (0:ℝ)<921/1000 by norm_num)
  have third := mul_pos (sub_pos.mpr lo) (neg_pos.mpr bn)
  have fourth := mul_nonneg (show (0:ℝ)≤39/100 by norm_num) (sub_nonneg.mpr bb)
  have endpoint := mul_pos (show 0<3/10-s by linarith only [ss])
    (show 0<531/2000+(39/200)*(s+3/10) by linarith only [sp])
  have identity :
      (c*d+s*r)*(c+s/2-1)-(c*r-s*d)*(s/2)-(13/50)*r=d*A+r*B := by
    dsimp only [A,B]
    linear_combination d*eu/2
  nlinarith only [first,second,third,fourth,endpoint,identity]

end N12Compact.Completion.OtherCases.C983.F4OuterScalars
