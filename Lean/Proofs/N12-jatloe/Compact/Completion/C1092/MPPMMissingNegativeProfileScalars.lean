import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C977CornerCubic

/-! Exact scalar steps shared by the weak and preceding-origin negative
missing-forward profiles. No side upper bound or numerical angle grid. -/
namespace N12Compact.C1092MPPMMissingNegativeProfile
open C977CornerCubic
set_option Elab.async false

theorem arc_gap {c s : ℝ} (cn : Normal c s) (sp : 0<s) :
    (413/500)*c*s<c+s-1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sum : c+s<14143/10000 := by
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤c+s-14143/10000 by linarith only [no])
      (show 0≤c+s+14143/10000 by linarith only [cp,sp])
    nlinarith only [square,sq_nonneg (c-s),cn.2.2]
  have product := mul_pos (mul_pos cp sp)
    (show 0<2-(413/500)*(1+c+s) by linarith only [sum])
  have identity : (1+c+s)*(c+s-1-(413/500)*c*s)=
      c*s*(2-(413/500)*(1+c+s)) := by
    linear_combination cn.2.2
  rw [←identity] at product
  have gap := pos_of_mul_pos_right product (by linarith only [cp,sp])
  linarith only [gap]

theorem half_width {c s b : ℝ} (cn : Normal c s) (width : 1<b*c+s) :
    1-b<(1+b)*C1092WallProfileScalars.half c s ∧
      C1092WallProfileScalars.half c s<1 := by
  have cb := normal_bounds cn
  have data := C1092WallProfileScalars.quarter_data c s
    (by linarith only [cb.1]) cn.1 cn.2.2
  let q := C1092WallProfileScalars.half c s
  have cosine : (1+q^2)*c=1-q^2 := data.2.2.2.1
  have sine : (1+q^2)*s=2*q := data.2.2.2.2
  have identity : (1+q^2)*(b*c+s-1)=(1-q)*((1+b)*q-(1-b)) := by
    linear_combination b*cosine+sine
  have product := mul_pos (show 0<1+q^2 by positivity) (sub_pos.mpr width)
  rw [identity] at product
  have gap := pos_of_mul_pos_right product
    (show 0≤1-q by change 0≤1-C1092WallProfileScalars.half c s; linarith only [data.2.1])
  have range := pos_of_mul_pos_left product gap.le
  exact ⟨by linarith only [gap],by linarith only [range]⟩

end N12Compact.C1092MPPMMissingNegativeProfile
