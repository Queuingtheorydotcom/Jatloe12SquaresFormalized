import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars
import Compact.Completion.C1092.MPPMPositiveRetainingSteepScalars

/-! Finite circle identities for STEEP-POSITIVE-NEGATIVE-PROFILE.
The printed half-angle quartic is exactly a product in the cosine;
the two final envelope bounds also use only the unit equation.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMSteepPositiveNegativeProfile.Scalars
open C977CornerCubic C1092MPPMNonpositivePredecessor
set_option Elab.async false
noncomputable section

def Pu (d t : ℝ) : ℝ := 2-d-(37/50)*t^2
def Qu (d t : ℝ) : ℝ := t*(1-(37/50)*d)
def Pv (d : ℝ) : ℝ := 13/50+(37/50)*d^2-d
def Qv (d t : ℝ) : ℝ := 1+t-(37/50)*d*t
def f (c s : ℝ) : ℝ := 1+c*s-c-s
def B (c s : ℝ) : ℝ := c-s+s^2-13/50

theorem current_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0≤1-Pu d t*c-Qu d t*s := by
  have eb := normal_bounds en
  have product := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
    (show 0≤6031*d-3969 by linarith only [eb.1])
  have identity : 1-(Pu d t)^2-(Qu d t)^2=
      (1-d)*(6031*d-3969)/2500 := by
    dsimp [Pu,Qu]
    linear_combination ((3531-1369*t^2)/2500)*en.2.2
  have small : (Pu d t)^2+(Qu d t)^2≤1^2 := by
    nlinarith only [identity,product]
  have bound := norm_le (Pu d t) (Qu d t) c s 1 cn.2.2 (by norm_num) small
  linarith only [bound]

theorem transverse_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<1-Pv d*c-Qv d t*s := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cs := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds cn
  have es := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds en
  have coefficient := mul_nonpos_of_nonpos_of_nonneg
    (show d-1≤0 by linarith only [eb.2.1])
    (show 0≤(37/50)*d-13/50 by linarith only [eb.1])
  have pn : Pv d≤0 := by dsimp [Pv]; nlinarith only [coefficient]
  have product := mul_nonneg en.1 (show 0≤d-7/10 by linarith only [eb.1])
  have qhigh : Qv d t<7/5 := by dsimp [Qv]; nlinarith only [product,es.2.2.2.1]
  have first := mul_nonpos_of_nonpos_of_nonneg pn cs.1.le
  have last := mul_le_mul_of_nonneg_right qhigh.le cn.1
  nlinarith only [first,last,cs.2.2.2.1]

theorem envelope {c s : ℝ} (cn : Normal c s) : f c s<43/500 ∧ 6/25≤B c s := by
  have cb := normal_bounds cn
  have cap : c+s<99/70 := by
    nlinarith only [cn.2.2,sq_nonneg (c-s),sq_nonneg (c+s-99/70)]
  have square := mul_pos (show 0<99/70-c-s by linarith only [cap])
    (show 0<99/70+c+s-2 by linarith only [cb.2.2.2.2.1])
  have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤1-(c+s)/2 by linarith only [cb.2.2.2.2.2])
  constructor
  · dsimp [f]
    nlinarith only [square,cn.2.2]
  · dsimp [B]
    nlinarith only [product,cn.2.2]

end
end N12Compact.C1092MPPMSteepPositiveNegativeProfile.Scalars
