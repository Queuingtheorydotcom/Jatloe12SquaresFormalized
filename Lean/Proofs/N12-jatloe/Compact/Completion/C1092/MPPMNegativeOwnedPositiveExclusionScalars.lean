import Compact.Completion.C1092.MPPMNegativeOwnedPositiveCeilingScalars

/-! NEGATIVE-OWNED-POSITIVE-OWNED-EXCLUSION: one exact norm
certificate and a simultaneous marker-cap comparison. Both complete
closed angle intervals are retained. Source only. -/
namespace N12Compact.C1092MPPMNegativeOwnedPositiveExclusion.Scalars
open C977CornerCubic C1092ShallowPositiveScalars C1092MPPMNonpositivePredecessor
set_option Elab.async false
noncomputable section

def Pu (d t : ℝ) : ℝ := 2-d-t+(11/25)*d*t
def Qu (d t : ℝ) : ℝ := 1-d+t-(11/25)*t^2
def Pf (c s : ℝ) : ℝ := 1-c-s+(13/20)*c*s+(7/20)*c^2
def Qf (c s : ℝ) : ℝ := 2-c+s-(7/20)*c*s-(13/20)*s^2
def bracket (y : ℝ) : ℝ := 1875*y^3-1450*y^2+1446*y-350

theorem recipient_bounds {d t : ℝ} (en : Normal d t)
    (small : t/(1+d)≤7/32) : t<21/50 ∧ 15*t<11*d := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  let y := t/(1+d)
  have data := C1092WallProfileScalars.quarter_data d t dp.le en.1 en.2.2
  have yn : 0≤y := data.1
  have yu : y≤7/32 := small
  have cosine : (1+y^2)*d=1-y^2 := data.2.2.2.1
  have sine : (1+y^2)*t=2*y := data.2.2.2.2
  have square := mul_nonneg (sub_nonneg.mpr yu) (show 0≤7/32+y by linarith only [yn])
  have first := mul_nonneg (sub_nonneg.mpr yu)
    (show 0≤2-(21/50)*(y+7/32) by linarith only [yu])
  have tScaled : 0<(1+y^2)*(21/50-t) := by
    nlinarith only [first,sine]
  have slopeScaled : 0<(1+y^2)*(11*d-15*t) := by
    nlinarith only [square,yu,cosine,sine]
  have tSmall := pos_of_mul_pos_right tScaled (show 0≤1+y^2 by positivity)
  have slope := pos_of_mul_pos_right slopeScaled (show 0≤1+y^2 by positivity)
  exact ⟨by linarith only [tSmall],by linarith only [slope]⟩

theorem longitudinal {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (tp : 0<t) (small : t/(1+d)≤7/32) : 0<1-Pu d t*c-Qu d t*s := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  let y := t/(1+d)
  have yp : 0<y := div_pos tp (by linarith only [dp])
  have yu : y≤7/32 := small
  have data := C1092WallProfileScalars.quarter_data d t dp.le en.1 en.2.2
  have dform : d=cosH y := by
    apply (eq_div_iff (half_den_pos y).ne').mpr
    have identity : (1+y^2)*d=1-y^2 := data.2.2.2.1
    nlinarith only [identity]
  have tform : t=sinH y := by
    apply (eq_div_iff (half_den_pos y).ne').mpr
    have identity : (1+y^2)*t=2*y := data.2.2.2.2
    nlinarith only [identity]
  have cube := mul_nonneg (sub_nonneg.mpr yu)
    (show 0≤y^2+y*(7/32)+(7/32)^2 by positivity)
  have negative : bracket y<0 := by
    dsimp [bracket]
    nlinarith only [cube,yu,sq_nonneg y]
  have identity : 625*(1+y^2)^2*(1-(Pu d t)^2-(Qu d t)^2)= -4*y*bracket y := by
    rw [dform,tform]
    dsimp [Pu,Qu,bracket,cosH,sinH]
    field_simp [(half_den_pos y).ne']
    <;> ring
  have scaled : 0<625*(1+y^2)^2*(1-(Pu d t)^2-(Qu d t)^2) := by
    rw [identity]
    nlinarith only [mul_pos yp (neg_pos.mpr negative)]
  have norm : (Pu d t)^2+(Qu d t)^2<1^2 := by
    have positive := pos_of_mul_pos_right scaled (show 0≤625*(1+y^2)^2 by positivity)
    linarith only [positive]
  have bound := norm_lt (Pu d t) (Qu d t) c s 1 cn.2.2 (by norm_num) norm
  linarith only [bound]

theorem transverse {c s d t : ℝ} (cn : Normal c s) (close : 87/100<c)
    (en : Normal d t) (small : t<21/50) : 0<1-Pf c s*d-Qf c s*t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have first := mul_nonneg cn.1 (show 0≤1-(13/20)*c by linarith only [cb.2.1])
  have decreasing := mul_nonneg (show 0≤c-87/100 by linarith only [close])
    (show 0≤1-(7/20)*(c+87/100) by linarith only [cb.2.1])
  have pcap : Pf c s<2/5 := by
    dsimp [Pf]
    nlinarith only [first,decreasing]
  have second := mul_nonneg cn.1 (show 0≤c-87/100 by linarith only [close])
  have qcap : Qf c s<33/25 := by
    dsimp [Qf]
    nlinarith only [second,close,sq_nonneg (s-1391/2600)]
  have pweighted := mul_lt_mul_of_pos_right pcap dp
  have qweighted := mul_le_mul_of_nonneg_right qcap.le en.1
  nlinarith only [pweighted,qweighted,eb.2.1,small]

end
end N12Compact.C1092MPPMNegativeOwnedPositiveExclusion.Scalars
