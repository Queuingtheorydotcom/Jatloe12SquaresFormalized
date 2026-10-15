import Compact.Geometry.CornerWallMarkerLongitudinal
import Compact.Geometry.CornerWallMarkerMixedBounds

/-! The final negative-L high-angle scalar with the genuine marker caps.
The sine-coordinate finite difference is nonnegative throughout the whole
canonical arc. Its certificate uses two unit disks and one linear bound;
there is no angle subdivision or extra singleton seed. Source uncompiled. -/
namespace N12Compact.CornerWallMarkerNegativeHighBounds

open C977CornerCubic C977CornerSectorBounds
open CornerWallMarkerLongitudinal CornerWallMarkerMixedBounds

private theorem seven_three {l r : ℝ} (ln : Normal l r) :
    7≤7*l+3*r := by
  have lb := normal_bounds ln
  have lp : 0≤l := by linarith only [lb.1]
  have bracket : 0≤21*l-20*r := by linarith only [ln.2.1,lp]
  have product := mul_nonneg ln.1 bracket
  have identity : (7*l+3*r)^2-49=2*r*(21*l-20*r) := by
    linear_combination 49*ln.2.2
  have nonnegative : 0≤7*l+3*r := by positivity
  by_contra no
  have positive := mul_pos
    (show 0<7-(7*l+3*r) by linarith only [no])
    (show 0<7+(7*l+3*r) by linarith only [nonnegative])
  nlinarith only [identity,product,positive]

private theorem coefficients {d t : ℝ} (wn : Normal d t)
    (small : t≤3/5) : 2≤X d t ∧ Y d t≤13/20 := by
  have wb := normal_bounds wn
  have dp : 0≤d := by linarith only [wb.1]
  have deficitLower : t^2/2≤1-d := by
    nlinarith only [wn.2.2,sq_nonneg (1-d)]
  have deficitProduct := mul_nonneg dp (sub_nonneg.mpr wb.2.1)
  have deficitUpper : 1-d≤t^2 := by
    nlinarith only [wn.2.2,deficitProduct]
  have mixed := mul_nonneg wn.1 (sub_nonneg.mpr wb.2.1)
  have first := mul_nonneg wn.1
    (show 0≤33/125-(3/20)*t by linarith only [small])
  have second := mul_nonneg wn.1
    (show 0≤7/20-(33/125)*t by linarith only [small])
  constructor
  · dsimp [X]
    nlinarith only [deficitLower,mixed,first]
  · dsimp [Y]
    nlinarith only [deficitUpper,mixed,second]

/-- A two-point arc certificate for the finite-difference numerator. -/
private theorem chord_margin {d t l r : ℝ}
    (wn : Normal d t) (ln : Normal l r) :
    0≤((l+d)^2-(r+t)^2)/2-(3/4)*(l+d)*(r+t)+
      (7/4)*(r+t)-(13/20)*(l+d) := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  let Q := l+d
  let R := r+t
  let x := Q-R
  have xp : 0≤x := by dsimp [x,Q,R]; linarith only [ln.2.1,wn.2.1]
  have xu : x≤2 := by
    dsimp [x,Q,R]
    linarith only [lb.2.1,wb.2.1,ln.1,wn.1]
  have dot := dot_le_one ln wn
  have disk : 0≤4-Q^2-R^2 := by
    dsimp [Q,R]
    nlinarith only [dot,ln.2.2,wn.2.2]
  have left := seven_three ln
  have wall := seven_three wn
  have line : 0≤R-7/5+(7/10)*x := by
    dsimp [R,x,Q]
    linarith only [left,wall]
  have product := mul_nonneg
    (show 0≤x+11/10 by linarith only [xp]) line
  have identity :
      (Q^2-R^2)/2-(3/4)*Q*R+(7/4)*R-(13/20)*Q =
      (7/40)*x^2+(1/50)*(2-x)+(3/8)*(4-Q^2-R^2)+
        (x+11/10)*(R-7/5+(7/10)*x) := by
    dsimp [x]
    ring
  change 0≤(Q^2-R^2)/2-(3/4)*Q*R+(7/4)*R-(13/20)*Q
  nlinarith only [identity,sq_nonneg x,xu,disk,product]

private noncomputable def response (d t l r : ℝ) : ℝ :=
  1+l*(G d t-t/d-X d t)+(t/d)*l^2+l*r-r*Y d t

/-- The response increases from the wall angle along the entire
remaining canonical arc, including both equal-angle endpoints. -/
private theorem response_order {d t l r : ℝ}
    (wn : Normal d t) (ln : Normal l r) (order : t≤r)
    (small : t≤3/5) (wide : 4/5≤d) :
    response d t d t≤response d t l r := by
  have wb := normal_bounds wn
  have lb := normal_bounds ln
  have dp : 0<d := by linarith only [wide]
  have lp : 0<l := by linarith only [lb.1]
  let Q := l+d
  let R := r+t
  let J := (Q^2-R^2)/2+R*(X d t-G d t+t/d)-
    (t/d)*Q*R-Y d t*Q
  have qp : 0<Q := by dsimp [Q]; linarith only [lp,dp]
  have qone : 1≤Q := by dsimp [Q]; linarith only [lb.1,wide]
  have rp : 0≤R := add_nonneg ln.1 wn.1
  have slope : t/d≤3/4 := by
    apply (div_le_iff₀ dp).2
    linarith only [small,wide]
  have bounds := coefficients wn small
  have gu := g_upper wn small
  have xg : 0≤X d t-G d t-1 := by linarith only [bounds.1,gu]
  have first := mul_nonneg rp xg
  have second := mul_nonneg (mul_nonneg (sub_nonneg.mpr slope) rp)
    (show 0≤Q-1 by linarith only [qone])
  have third := mul_nonneg (sub_nonneg.mpr bounds.2) qp.le
  have disk := chord_margin wn ln
  have identity :
      J-((Q^2-R^2)/2-(3/4)*Q*R+(7/4)*R-(13/20)*Q)=
      R*(X d t-G d t-1)+(3/4-t/d)*R*(Q-1)+(13/20-Y d t)*Q := by
    dsimp [J]
    ring
  have jp : 0≤J := by
    change 0≤(Q^2-R^2)/2-(3/4)*Q*R+(7/4)*R-(13/20)*Q at disk
    nlinarith only [identity,disk,first,second,third]
  have chord : (l-d)*(l+d)=-(r-t)*(r+t) := by
    linear_combination ln.2.2-wn.2.2
  have crossChord :
      (l+d)*(l*r-d*t)-(r-t)*((l+d)^2-(r+t)^2)/2=0 := by
    linear_combination ((r+t)/2)*(ln.2.2-wn.2.2)
  have difference : Q*(response d t l r-response d t d t)=(r-t)*J := by
    dsimp [Q,R,J,response]
    linear_combination
      (G d t-t/d-X d t+(t/d)*(l+d))*chord+crossChord
  have product := mul_nonneg (sub_nonneg.mpr order) jp
  have scaled : 0≤Q*(response d t l r-response d t d t) := by
    nlinarith only [difference,product]
  have unscaled := nonneg_of_mul_nonneg_right scaled qp
  linarith only [unscaled]

private theorem endpoint {d t : ℝ} (wn : Normal d t)
    (small : t≤3/5) (wide : 4/5≤d) : 0≤response d t d t := by
  have dp : 0<d := by linarith only [wide]
  have disk := linear_margin wn wn wn (le_refl t) small wide
  have supportIdentity : d*X d t+t*Y d t=3*d+(457/500)*t-1 := by
    dsimp [X,Y]
    linear_combination -(1+(92/125)*t)*wn.2.2
  have identity :
      response d t d t-
        (1+d*(G d t+t+(1-t)/d-3)-t*(1-d)) =
      -1+t+3*d-d*X d t-t*Y d t := by
    dsimp [response]
    field_simp [ne_of_gt dp]
    <;> ring
  nlinarith only [disk,supportIdentity,identity,wn.1]

/-- The complete high-r scalar for the O-v / negative-L-v selector,
using the genuine top and northwest marker bounds. -/
theorem margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : t≤r)
    (small : t≤3/5) (wide : 4/5≤d) :
    0≤1+(l/c)*boundary c s+(l/c)*(s*l+c*r)-r*Y d t-l*X d t := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have dc := cosine_order wn on order
  have cp : 0<c := by linarith only [wide,dc]
  have dp : 0<d := by linarith only [wide]
  have lp : 0≤l := by linarith only [lb.1]
  have first := mul_nonneg dp.le (sub_nonneg.mpr order)
  have second := mul_nonneg wn.1 (sub_nonneg.mpr dc)
  have slope : s/c≤t/d := by
    apply (div_le_div_iff₀ cp dp).2
    nlinarith only [first,second]
  have gmonotone := g_order on wn order small wide
  have base := endpoint wn small wide
  have monotone := response_order wn ln leftOrder small wide
  have gterm := mul_nonneg lp (sub_nonneg.mpr gmonotone)
  have slopeTerm := mul_nonneg (mul_nonneg (sub_nonneg.mpr slope) lp)
    (sub_nonneg.mpr lb.2.1)
  have identity :
      (1+(l/c)*boundary c s+(l/c)*(s*l+c*r)-r*Y d t-l*X d t)-
        response d t l r =
      l*(G c s-G d t)+(t/d-s/c)*l*(1-l) := by
    dsimp [response,G]
    field_simp [ne_of_gt cp,ne_of_gt dp]
    <;> ring
  nlinarith only [base,monotone,gterm,slopeTerm,identity]

#print axioms margin
end N12Compact.CornerWallMarkerNegativeHighBounds
