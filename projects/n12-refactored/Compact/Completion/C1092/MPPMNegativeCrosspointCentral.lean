import Compact.Completion.C1092.MPPMNegativeCrosspointSupportScalars
import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Clamp
import Compact.Completion.CommonCases.UnitCircleChord

/-! NEGATIVE-WALL-SCALARS section 2 on the full closed domain. The
three genuine support pieces are interpolated by the unit-circle chord
lemma. At the successor alignment, multiplication by 1+d replaces the
manuscript's half-angle identity, including t=0 without a division by t.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

theorem shallow_bounds {d t : ℝ} (en : Normal d t) (shallow : 8*t≤3*d) :
    93/100≤d ∧ t≤9/25 := by
  have eb := normal_bounds en
  have product := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0≤3*d+8*t by linarith only [eb.1,en.1])
  constructor
  · apply le_of_not_gt
    intro bad
    have gap := mul_pos (show 0<93/100-d by linarith only [bad])
      (show 0<93/100+d by linarith only [eb.1])
    nlinarith only [gap,product,en.2.2]
  · apply le_of_not_gt
    intro bad
    have gap := mul_pos (show 0<t-9/25 by linarith only [bad])
      (show 0<t+9/25 by linarith only [en.1])
    nlinarith only [gap,product,en.2.2]

private theorem endpoint_C {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (shallow : 8*t≤3*d) :
    0≤ell c s d t*(c+s-1)-s*t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have sb := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have enon : 0≤ell c s d t := by
    dsimp [ell]
    exact add_nonneg (mul_nonneg (by linarith only [cb.1]) en.1)
      (mul_nonneg cn.1 (by linarith only [eb.1]))
  have first := mul_nonneg enon
    (show 0≤c+s-7/5 by linarith only [sb.2.2.1])
  have last := mul_nonneg (show 0≤3*d/8-t by linarith only [shallow])
    (show 0≤s-(2/5)*c by linarith only [steep,sb.1])
  have remainder := mul_nonneg (show 0≤d by linarith only [eb.1])
    (show 0≤s/40+(3/20)*c by linarith only [cn.1,cb.1])
  dsimp [ell] at enon first ⊢
  nlinarith only [first,last,remainder]

private theorem endpoint_E {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (shallow : 8*t≤3*d) : 0≤ell c s d t*(d+t-1)-s*t := by
  have eb := normal_bounds en
  have small := shallow_bounds en shallow
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤1+d-t by linarith only [en.2.1])
  have last := mul_nonneg cn.1
    (show 0≤1-2*t by linarith only [small.2])
  have bracket : 0≤c*(1+d-t)-s*(d+t) := by nlinarith only [first,last]
  have product := mul_nonneg (sq_nonneg t) bracket
  have identity : (1+d)*(ell c s d t*(d+t-1)-s*t)=
      t^2*(c*(1+d-t)-s*(d+t)) := by
    dsimp [ell]
    linear_combination (c*t+s*(d+t))*en.2.2
  have weighted : 0≤(1+d)*(ell c s d t*(d+t-1)-s*t) := by
    rw [identity]
    exact product
  exact nonneg_of_mul_nonneg_right weighted (by linarith only [eb.1])

theorem low_below {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t) :
    (2*ell c s d t+2*s*t)*h+2*s*d*r≤width c s d t h r := by
  have first := mul_le_mul_of_nonneg_left (neg_le_abs (deltaC c s h r)) en.1
  have last := mul_le_mul_of_nonneg_left (neg_le_abs (deltaE d t h r)) cn.1
  dsimp [width,ell,kC,kE,deltaC,deltaE] at *
  nlinarith only [first,last]

theorem middle_below {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t) :
    2*ell c s d t*h+2*ell c s d t*r≤width c s d t h r := by
  have first := mul_le_mul_of_nonneg_left (le_abs_self (deltaC c s h r)) en.1
  have last := mul_le_mul_of_nonneg_left (neg_le_abs (deltaE d t h r)) cn.1
  dsimp [width,ell,kC,kE,deltaC,deltaE] at *
  nlinarith only [first,last]

theorem high_below {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t) :
    2*c*t*h+(2*ell c s d t+2*s*t)*r≤width c s d t h r := by
  have first := mul_le_mul_of_nonneg_left (le_abs_self (deltaC c s h r)) en.1
  have last := mul_le_mul_of_nonneg_left (le_abs_self (deltaE d t h r)) cn.1
  dsimp [width,ell,kC,kE,deltaC,deltaE] at *
  nlinarith only [first,last]

theorem width_lower {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (shallow : 8*t≤3*d) (q : Quarter h r) :
    2*ell c s d t+2*s*t≤width c s d t h r := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0≤d := by linarith only [eb.1]
  have tn : 0≤t := en.1
  have enon : 0≤ell c s d t := by
    dsimp [ell]
    exact add_nonneg (mul_nonneg cp en.1) (mul_nonneg cn.1 dp)
  have st : 0≤s*t := mul_nonneg cn.1 en.1
  have left := endpoint_C cn en steep shallow
  have right := endpoint_E cn en shallow
  have upper : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  have eq : t^2+d^2=1 := by nlinarith only [en.2.2]
  by_cases low : r≤s
  · have first : 0≤-(2*ell c s d t+2*s*t)+
        (2*ell c s d t+2*s*t)*1+(2*s*d)*0 := by ring_nf
    have last : 0≤-(2*ell c s d t+2*s*t)+
        (2*ell c s d t+2*s*t)*c+(2*s*d)*s := by
      dsimp [ell] at left ⊢
      nlinarith only [left]
    have chord := CommonCases.UnitCircleChord.linear_nonnegative
      (by norm_num : (0:ℝ)≤1) cp q.cosine (by norm_num : (1:ℝ)^2+0^2=1)
      cn.2.2 q.unit q.sine low (by linarith only [enon,st]) first last
    have below := low_below (h:=h) (r:=r) cn en
    linarith only [chord,below]
  · have low : s≤r := (lt_of_not_ge low).le
    by_cases high : r≤d
    · have first : 0≤-(2*ell c s d t+2*s*t)+(2*ell c s d t)*c+
          (2*ell c s d t)*s := by nlinarith only [left]
      have last : 0≤-(2*ell c s d t+2*s*t)+(2*ell c s d t)*t+
          (2*ell c s d t)*d := by nlinarith only [right]
      have chord := CommonCases.UnitCircleChord.linear_nonnegative cp en.1 q.cosine
        cn.2.2 eq q.unit low high (by linarith only [enon]) first last
      have below := middle_below (h:=h) (r:=r) cn en
      linarith only [chord,below]
    · have first : 0≤-(2*ell c s d t+2*s*t)+(2*c*t)*t+
          (2*ell c s d t+2*s*t)*d := by
        dsimp [ell] at right ⊢
        nlinarith only [right]
      have last : 0≤-(2*ell c s d t+2*s*t)+(2*c*t)*0+
          (2*ell c s d t+2*s*t)*1 := by ring_nf
      have chord := CommonCases.UnitCircleChord.linear_nonnegative en.1
        (by norm_num : (0:ℝ)≤0) q.cosine eq (by norm_num : (0:ℝ)^2+1^2=1)
        q.unit (lt_of_not_ge high).le upper (by positivity : 0≤2*c*t) first last
      have below := high_below (h:=h) (r:=r) cn en
      linarith only [chord,below]

theorem G00_lower {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (shallow : 8*t≤3*d) (q : Quarter h r) :
    (77/5000)*t≤G00 c s d t h r := by
  have wb := width_lower cn en steep shallow q
  have sb := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have gap := mul_nonneg en.1
    (show 0≤1-c-(13/50)*s-77/5000 by linarith only [sb.1,sb.2.1])
  dsimp [G00,C0,E0,ell] at *
  nlinarith only [wb,gap]

theorem G00_nonnegative {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (shallow : 8*t≤3*d) (q : Quarter h r) :
    0≤G00 c s d t h r :=
  le_trans (mul_nonneg (by norm_num) en.1) (G00_lower cn en steep shallow q)

end
#print axioms width_lower
#print axioms G00_nonnegative
end N12Compact.C1092MPPMNegativeCrosspointSupport
