import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Exact continuous margins for the first standardized MMMM central pair.
These inequalities contain no point-owner or wall assumptions. -/
namespace N12Compact.C1092MMMMPairScalars
open C977CornerCubic
set_option Elab.async false

theorem sine_bound {b t : ℝ} (bn : Normal b t) : t ≤ 5/7 := by
  have bb := normal_bounds bn
  have order := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤b+t by linarith only [bb.1,bn.1])
  nlinarith only [order,bn.2.2,sq_nonneg (t-5/7)]

theorem negative_transverse_ge {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (order : 0 ≤ b*r-t*d) :
    d*(1-b+t-t^2)+r*(-39/100-b-t+b*t) ≤ 0 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have bp : 0 < b := by linarith only [bb.1]
  have bt : b*t ≤ 1/2 := by nlinarith only [bn.2.2,sq_nonneg (b-t)]
  have gn : -39/100-b-t+b*t ≤ 0 := by linarith only [bb.2.2.2.2.1,bt]
  have cancel : b*(1-b+t-t^2)+t*(-39/100-b-t+b*t)=b-1-(39/100)*t := by
    linear_combination -bn.2.2
  have first := mul_nonpos_of_nonneg_of_nonpos dp.le
    (show b-1-(39/100)*t ≤ 0 by linarith only [bb.2.1,bn.1])
  have last := mul_nonpos_of_nonneg_of_nonpos order gn
  have identity : b*(d*(1-b+t-t^2)+r*(-39/100-b-t+b*t))=
      d*(b-1-(39/100)*t)+(b*r-t*d)*(-39/100-b-t+b*t) := by
    calc
      _ = d*(b*(1-b+t-t^2)+t*(-39/100-b-t+b*t))+
          (b*r-t*d)*(-39/100-b-t+b*t) := by ring
      _ = _ := by rw [cancel]
  exact (mul_le_mul_left bp).mp (by rw [mul_zero,identity]; linarith only [first,last])

theorem one_minus {b t : ℝ} (bn : Normal b t) : 1-b ≤ (3/5)*t^2 := by
  have bb := normal_bounds bn
  have bp : 0 < 1+b := by linarith only [bb.1]
  have product := mul_nonneg (sq_nonneg t)
    (show 0 ≤ (3/5)*(1+b)-1 by linarith only [bb.1])
  have identity : (1+b)*((3/5)*t^2-(1-b))=t^2*((3/5)*(1+b)-1) := by
    linear_combination bn.2.2
  have nonneg := nonneg_of_mul_nonneg_right (by rw [identity]; exact product) bp
  linarith only [nonneg]

theorem negative_transverse_le {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (tp : 0 < t) :
    d*(1-b-(13/20)*t^2-(1/25)*b*t)+
      r*(-7/20-(1/25)*t^2+(13/20)*b*t-t) < 0 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have bp : 0 < b := by linarith only [bb.1]
  have baseline := one_minus bn
  have cross := mul_pos bp tp
  have fn : 1-b-(13/20)*t^2-(1/25)*b*t < 0 := by
    nlinarith only [baseline,cross,sq_nonneg t]
  have bt := mul_nonneg tp.le (sub_nonneg.mpr bb.2.1)
  have gn : -7/20-(1/25)*t^2+(13/20)*b*t-t ≤ 0 := by
    nlinarith only [bt,bn.1,sq_nonneg t]
  have first := mul_neg_of_pos_of_neg dp fn
  have last := mul_nonpos_of_nonneg_of_nonpos dn.1 gn
  linarith only [first,last]

theorem negative_longitudinal_ge {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (order : 0 ≤ b*r-t*d) :
    b*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
      t*(17/20-r-(3/20)*r^2+(7/20)*d*r) ≤ 0 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have rp : r^2 ≤ 1/2 := by
    have h := mul_nonneg (sub_nonneg.mpr dn.2.1) (show 0≤d+r by linarith only [db.1,dn.1])
    nlinarith only [h,dn.2.2]
  have rb := sine_bound dn
  have dr := mul_nonneg dp.le dn.1
  have gn : 0 ≤ 17/20-r-(3/20)*r^2+(7/20)*d*r := by
    nlinarith only [rb,rp,dr]
  have cancel : d*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
      r*(17/20-r-(3/20)*r^2+(7/20)*d*r)=(7/10)*(d+r)-1 := by
    linear_combination (-1-(3/20)*r)*dn.2.2
  have first := mul_nonpos_of_nonneg_of_nonpos (by linarith only [bb.1] : 0≤b)
    (show (7/10)*(d+r)-1≤0 by linarith only [db.2.2.2.2.2])
  have last := mul_nonneg order gn
  have identity : d*(b*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
      t*(17/20-r-(3/20)*r^2+(7/20)*d*r))=
      b*((7/10)*(d+r)-1)-(b*r-t*d)*(17/20-r-(3/20)*r^2+(7/20)*d*r) := by
    calc
      _ = b*(d*(7/10-d-(7/20)*r^2-(3/20)*d*r)+
          r*(17/20-r-(3/20)*r^2+(7/20)*d*r))-
          (b*r-t*d)*(17/20-r-(3/20)*r^2+(7/20)*d*r) := by ring
      _ = _ := by rw [cancel]
  exact (mul_le_mul_left dp).mp (by rw [mul_zero,identity]; linarith only [first,last])

theorem negative_longitudinal_le {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t) :
    b+t-(b*d+t*r)*(1-(7/20)*(d+r)) ≤ 27/28 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have q0 : 0 ≤ 1-(7/20)*(d+r) := by linarith only [db.2.2.2.2.2]
  have order := mul_nonneg (sub_nonneg.mpr bn.2.1) (sub_nonneg.mpr dn.2.1)
  have alpha : 0 ≤ 2*(b*d+t*r)-(b+t)*(d+r) := by nlinarith only [order]
  have first := mul_nonneg q0 alpha
  have chord := mul_nonneg (show 0≤d+r-1 by linarith only [db.2.2.2.2.1])
    (show 0≤13/20-(7/20)*(d+r) by linarith only [db.2.2.2.2.2])
  have interval : 13/20 ≤ (d+r)*(1-(7/20)*(d+r)) := by nlinarith only [chord]
  have last := mul_nonneg (show 0≤b+t by linarith only [bb.2.2.2.2.1])
    (sub_nonneg.mpr interval)
  nlinarith only [first,last,bb.2.2.2.2.2]

theorem positive_longitudinal {d r : ℝ} (dn : Normal d r) :
    7/10-d-(7/20)*r^2-(3/20)*d*r ≤ 0 ∧
      -17/20+r+(3/20)*r^2-(7/20)*d*r < 0 := by
  have db := normal_bounds dn
  have rb := sine_bound dn
  have dr := mul_nonneg (by linarith only [db.1] : 0≤d) dn.1
  have order := mul_nonneg dn.1 (sub_nonneg.mpr dn.2.1)
  constructor
  · nlinarith only [db.1,dr,sq_nonneg r]
  · nlinarith only [order,rb,sq_nonneg r]

theorem positive_transverse {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (tp : 0 < t) :
    -d*(b+t-1-(61/100)*b*t)+r*(t-b-39/100-(61/100)*t^2) < 0 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have bp : 0 < b := by linarith only [bb.1]
  have sum : 1 < b+t := by
    have cross := mul_pos bp tp
    nlinarith only [bn.2.2,cross,bb.2.2.2.2.1]
  have identity : b+t-1-(61/100)*b*t=
      (b+t-1)*(1-(61/200)*(b+t+1)) := by
    linear_combination (61/200)*bn.2.2
  have positive : 0 < b+t-1-(61/100)*b*t := by
    rw [identity]
    exact mul_pos (by linarith only [sum]) (by linarith only [bb.2.2.2.2.2])
  have first := mul_neg_of_pos_of_neg dp (neg_neg_of_pos positive)
  have last := mul_nonpos_of_nonneg_of_nonpos dn.1
    (show t-b-39/100-(61/100)*t^2 ≤ 0 by nlinarith only [bn.2.1,sq_nonneg t])
  linarith only [first,last]

theorem small_of_support {d r b t a u v : ℝ} (dn : Normal d r) (bn : Normal b t)
    (ha : 1 < a) (up : 0 < u) (vp : 0 < v) (cap : u ≤ (7/20)*(d+r))
    (support : a*(1+b*r+t*d) ≤ b+t+(b*r+t*d)*u-(b*d-t*r)*v) :
    r < 7/50 ∧ 99/100 < d := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have alpha : 0 ≤ b*d-t*r := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1) dp.le
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    nlinarith only [first,last]
  have k : 0 ≤ b*r+t*d := by
    have first := mul_nonneg (by linarith only [bb.1] : 0≤b) dn.1
    have last := mul_nonneg bn.1 dp.le
    linarith only [first,last]
  have strict := mul_pos (sub_pos.mpr ha) (show 0<1+b*r+t*d by linarith only [k])
  have weight := mul_nonneg k (sub_nonneg.mpr cap)
  have last := mul_nonneg alpha vp.le
  let F := 1-r*(1-(7/20)*(d+r))
  let G := 1-d*(1-(7/20)*(d+r))
  have projection : 1 < b*F+t*G := by dsimp [F,G]; nlinarith only [strict,weight,last,support]
  have projectionSquare := mul_pos (show 0<b*F+t*G-1 by linarith only [projection])
    (show 0<b*F+t*G+1 by linarith only [projection])
  have cauchy : (b*F+t*G)^2+(t*F-b*G)^2=F^2+G^2 := by
    linear_combination (F^2+G^2)*bn.2.2
  have norm : 1 < F^2+G^2 := by nlinarith only [cauchy,projectionSquare,sq_nonneg (t*F-b*G)]
  have polynomial : F^2+G^2-1=2-(27/10)*(d+r)+(329/400)*(d+r)^2 := by
    dsimp [F,G]
    linear_combination (1-(7/20)*(d+r))^2*dn.2.2
  have sum : d+r < 113/100 := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonneg (show 0≤d+r-113/100 by linarith only [no])
      (show 0≤27/10-(329/400)*(d+r+113/100) by linarith only [db.2.2.2.2.2])
    have positive : 0 < 2-(27/10)*(d+r)+(329/400)*(d+r)^2 := by
      rw [← polynomial]
      exact sub_pos.mpr norm
    nlinarith only [product,positive]
  have rb := sine_bound dn
  have small : r < 7/50 := by
    apply lt_of_not_ge
    intro no
    have curve := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤r-7/50 by linarith only [no])
      (show 2*r-99/50≤0 by linarith only [rb])
    have gap := mul_pos (show 0<113/100-r-d by linarith only [sum])
      (show 0<113/100-r+d by linarith only [db.1,rb])
    nlinarith only [curve,gap,dn.2.2]
  have close : 99/100 < d := by
    apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤99/100-d by linarith only [no])
      (show 0≤99/100+d by linarith only [db.1])
    have strict := mul_pos (show 0<7/50-r by linarith only [small])
      (show 0<7/50+r by linarith only [dn.1])
    nlinarith only [bound,strict,dn.2.2]
  exact ⟨small,close⟩

theorem small_negative_longitudinal {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (small : r < 7/50) (close : 99/100 < d) :
    b*(27/20-d-(7/20)*d*r-(17/20)*r^2)+
      t*(1+r-(17/20)*d*r+(7/20)*r^2) < 1 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  let F := 27/20-d-(7/20)*d*r-(17/20)*r^2
  let G := 1+r-(17/20)*d*r+(7/20)*r^2
  have dr : 0 ≤ d*r := mul_nonneg (by linarith only [db.1]) dn.1
  have dru : d*r ≤ r := by
    have h := mul_nonneg dn.1 (sub_nonneg.mpr db.2.1)
    nlinarith only [h]
  have r2 : r^2 ≤ (7/50)^2 := by
    have h := mul_nonneg (show 0≤7/50-r by linarith only [small])
      (show 0≤7/50+r by linarith only [dn.1])
    nlinarith only [h]
  have fp : 0 ≤ F := by dsimp [F]; nlinarith only [db.2.1,dru,small,r2]
  have fu : F ≤ 9/25 := by dsimp [F]; nlinarith only [close,dr,sq_nonneg r]
  have gl : 1 ≤ G := by dsimp [G]; nlinarith only [dru,dn.1,sq_nonneg r]
  have one := one_minus dn
  have dc := mul_nonneg dn.1 (show 0≤d-99/100 by linarith only [close])
  have curve := mul_nonneg dn.1 (show 0≤47/250-(1/10)*r by linarith only [small])
  have sum : F+G ≤ 27/20 := by dsimp [F,G]; nlinarith only [one,dc,curve]
  have gp : 0 ≤ G := le_trans (by norm_num) gl
  have order : F ≤ G := le_trans fu (le_trans (by norm_num) gl)
  have first := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (mul_nonneg (show 0≤b+t by linarith only [bb.2.2.2.2.1])
      (mul_nonneg (sub_nonneg.mpr order) (add_nonneg gp fp)))
  have last := mul_nonneg (sq_nonneg (b-t))
    (mul_nonneg fp gp)
  have identity : (F+G)^2-2*(b*F+t*G)^2=
      (b-t)*(b+t)*(G-F)*(G+F)+2*(b-t)^2*F*G := by
    linear_combination -(F+G)^2*bn.2.2
  have gap : 0 ≤ (F+G)^2-2*(b*F+t*G)^2 := by
    rw [identity]
    convert add_nonneg first (mul_nonneg (show (0:ℝ)≤2 by norm_num) last) using 1 <;> ring
  have cap : (F+G)^2 ≤ (27/20)^2 :=
    (sq_le_sq₀ (add_nonneg fp gp) (by norm_num)).mpr sum
  have squared : 2*(b*F+t*G)^2 ≤ (27/20)^2 := le_trans (sub_nonneg.mp gap) cap
  change b*F+t*G < 1
  generalize b*F+t*G = x at squared ⊢
  nlinarith only [squared,sq_nonneg (x-1)]

theorem small_negative_transverse {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (small : r < 7/50) (close : 99/100 < d) (tp : 0 < t) :
    d*(1-b-(13/20)*t^2-(1/25)*b*t)+
      r*(7/20+(1/25)*t^2-(13/20)*b*t+t) < r/2 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [db.1]
  have bp : 0 < b := by linarith only [bb.1]
  have product := mul_nonneg (sq_nonneg t)
    (show 0≤(59/100)*(1+b)-1 by linarith only [bb.1])
  have identity : (1+b)*((59/100)*t^2-(1-b))=t^2*((59/100)*(1+b)-1) := by
    linear_combination bn.2.2
  have tight : 1-b ≤ (59/100)*t^2 := by
    have h := nonneg_of_mul_nonneg_right (by rw [identity]; exact product)
      (show 0<1+b by linarith only [bb.1])
    linarith only [h]
  let f := 1-b-(13/20)*t^2-(1/25)*b*t
  let g := 7/20+(1/25)*t^2-(13/20)*b*t+t
  have cross := mul_pos bp tp
  have fn : f < 0 := by dsimp [f]; nlinarith only [tight,cross,sq_nonneg t]
  by_cases low : g ≤ 1/2
  · have first := mul_neg_of_pos_of_neg dp fn
    change d*f+r*g<r/2
    calc
      _ < 0+r*g := add_lt_add_right first _
      _ = r*g := zero_add _
      _ ≤ r*(1/2) := mul_le_mul_of_nonneg_left low dn.1
      _ = _ := by ring
  · have first := mul_lt_mul_of_neg_right close fn
    have last := mul_lt_mul_of_pos_right small (show 0<g-1/2 by linarith only [low])
    have fw := mul_nonneg (by norm_num : (0:ℝ)≤99/100)
      (show 0≤-(3/50)*t^2-(1/25)*b*t-f by dsimp [f]; nlinarith only [tight])
    have bw := mul_nonneg tp.le (show 0≤b-7/10 by linarith only [bb.1])
    have quadratic : -21/1000+(2429/50000)*t-(269/5000)*t^2<0 := by
      nlinarith only [sq_nonneg (t-2429/5380)]
    change d*f+r*g<r/2
    dsimp [f,g] at first last fw ⊢
    nlinarith only [first,last,fw,bw,quadratic]

theorem small_positive_longitudinal {d r : ℝ} (dn : Normal d r)
    (small : r < 7/50) (close : 99/100 < d) :
    7/10-d-(7/20)*r^2+(3/20)*d*r < 0 ∧
      -17/20-r+(3/20)*r^2+(7/20)*d*r < 0 := by
  have db := normal_bounds dn
  have dru : d*r ≤ r := by
    have h := mul_nonneg dn.1 (sub_nonneg.mpr db.2.1)
    nlinarith only [h]
  have r2 : r^2 ≤ (7/50)^2 := by
    have h := mul_nonneg (show 0≤7/50-r by linarith only [small])
      (show 0≤7/50+r by linarith only [dn.1])
    nlinarith only [h]
  constructor <;> nlinarith only [close,small,dru,r2,sq_nonneg r,dn.1]

theorem small_positive_transverse {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (small : r < 7/50) (close : 99/100 < d)
    (steep : 9/20 < t) (cosine : b < 9/10) :
    0 < d*(b+t-1-(61/100)*b*t)-r*(b-t-11/100+(61/100)*t^2) := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have tb := sine_bound bn
  have t2 : t^2 ≤ 1/2 := by
    have h := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤b+t by linarith only [bb.1,bn.1])
    nlinarith only [h,bn.2.2]
  have sum : 67/50 < b+t := by
    apply lt_of_not_ge; intro no
    have curve := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤t-9/20 by linarith only [steep])
      (show 2*t-89/50≤0 by linarith only [tb])
    have cap := mul_nonneg (show 0≤67/50-t-b by linarith only [no])
      (show 0≤67/50-t+b by linarith only [tb,bb.1])
    nlinarith only [curve,cap,bn.2.2]
  have increasing := mul_pos (show 0<b+t-67/50 by linarith only [sum])
    (show 0<1-(61/200)*(b+t+67/50) by linarith only [bb.2.2.2.2.2])
  have identity : b+t-1-(61/100)*b*t-48671/500000=
      (b+t-67/50)*(1-(61/200)*(b+t+67/50)) := by
    linear_combination (61/200)*bn.2.2
  have K : 19/200 < b+t-1-(61/100)*b*t := by nlinarith only [increasing,identity]
  have J : b-t-11/100+(61/100)*t^2 < 129/200 := by
    nlinarith only [cosine,steep,t2]
  have first := mul_lt_mul_of_pos_right close
    (show 0<b+t-1-(61/100)*b*t by linarith only [K])
  have base := mul_lt_mul_of_pos_left K (by norm_num : (0:ℝ)<99/100)
  have last := mul_le_mul_of_nonneg_left J.le dn.1
  have strict := mul_lt_mul_of_pos_right small (by norm_num : (0:ℝ)<129/200)
  nlinarith only [first,base,last,strict]

#print axioms small_of_support
end N12Compact.C1092MMMMPairScalars
