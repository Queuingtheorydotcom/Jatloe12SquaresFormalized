import Compact.Geometry.C977CornerCubic

/-! Continuous support coefficients for the positive opposite central
square. The whole canonical opposite arc is covered by one coefficient
order and one sum bound, without an angle partition. -/
namespace N12Compact.FullAuxWallPositiveMargins

open C977CornerCubic
set_option Elab.async false

noncomputable def F (c s : ℝ) : ℝ := 2/5+s-(37/50)*c*s+(2/5)*s^2
noncomputable def G (c s : ℝ) : ℝ := 2-c-(37/50)*s^2-(2/5)*c*s

theorem coefficients {c s : ℝ} (an : Normal c s) (narrow : 4*s≤c) :
    0≤F c s ∧ F c s≤G c s ∧ F c s+G c s≤7/5 := by
  have ab := normal_bounds an
  have cp : 0<c := by linarith only [ab.1]
  have sp := an.1
  have su : s≤1/4 := by linarith only [narrow,ab.2.1]
  have range := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤c+4*s by linarith only [cp,sp])
  have cl : (24/25 : ℝ)≤c := by
    apply le_of_not_gt
    intro bad
    have square := mul_pos (sub_pos.mpr bad)
      (show 0<(24/25 : ℝ)+c by linarith only [cp])
    nlinarith only [square,range,an.2.2]
  have deficitProduct := mul_nonneg (sub_nonneg.mpr ab.2.1)
    (show 0≤c-(1/2 : ℝ) by linarith only [cl])
  have deficit : 1-c≤(2/3)*s^2 := by
    nlinarith only [deficitProduct,an.2.2]
  have nonnegative : 0≤F c s := by
    have product := mul_nonneg sp
      (show 0≤1-(37/50)*c by linarith only [ab.2.1])
    dsimp [F]
    nlinarith only [product,sq_nonneg s]
  have order : F c s≤G c s := by
    have smallSquare := mul_nonneg sp (sub_nonneg.mpr su)
    have cs := mul_nonneg cp.le sp
    dsimp [F,G]
    nlinarith only [smallSquare,cs,ab.2.1,su]
  have sum : F c s+G c s≤7/5 := by
    have narrowWeight := mul_nonneg sp (sub_nonneg.mpr narrow)
    have cosineWeight := mul_nonneg sp (sub_nonneg.mpr cl)
    dsimp [F,G]
    nlinarith only [deficit,narrowWeight,cosineWeight,sp]
  exact ⟨nonnegative,order,sum⟩

theorem margin {c s C S : ℝ}
    (an : Normal c s) (cn : Normal C S) (narrow : 4*s≤c) :
    C*F c s+S*G c s≤1 := by
  have values := coefficients an narrow
  have cb := normal_bounds cn
  have total : 0≤F c s+G c s := by linarith only [values.1,values.2.1]
  have order := mul_nonneg (sub_nonneg.mpr values.2.1)
    (sub_nonneg.mpr cn.2.1)
  have arc := mul_nonneg total (sub_nonneg.mpr cb.2.2.2.2.2)
  nlinarith only [order,arc,values.2.2]

#print axioms coefficients
#print axioms margin
end N12Compact.FullAuxWallPositiveMargins
