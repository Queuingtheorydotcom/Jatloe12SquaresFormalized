import Compact.Completion.OtherCases.SupportBands
import Compact.Completion.C1092.WholeSupports

/-! Whole-square comparisons (9)--(12) of C983-F4-TOP-ONLY-8208-ENDING
section 2.1. They also apply literally in the mixed-negative chapter.
Both relative-angle signs are retained, including equality. -/
namespace N12Compact.Completion.OtherCases.C983.F4SoutheastSignSupports
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

structure Data (E : OpenSquare) : Prop where
  cosine : 4/5<E.c
  cosineUpper : E.c<1
  sine : 0<E.s
  sineUpper : E.s<1/2
  lowerU : E.loU<E.c-1
  lowerV : E.loV< -(7/20)*(E.c+E.s)
  upperU : (13/50)*E.c<E.loU+E.side
  upperV : -(13/50)*E.s<E.loV+E.side

private theorem coefficients (E : OpenSquare) (data : Data E) :
    (1-E.c)*(13/50-(37/50)*E.c)<0 ∧
    E.s-(37/50)*E.c*E.s-13/50<0 ∧
    E.s*((37/50)*E.c-1)<0 := by
  have first := mul_neg_of_pos_of_neg
    (show 0<1-E.c by linarith only [data.cosineUpper])
    (show 13/50-(37/50)*E.c<0 by linarith only [data.cosine])
  have middle := mul_pos (show 0<E.c-4/5 by linarith only [data.cosine]) data.sine
  have last := mul_neg_of_pos_of_neg data.sine
    (show (37/50)*E.c-1<0 by linarith only [data.cosineUpper])
  exact ⟨first,by nlinarith only [middle,data.sineUpper],last⟩

/-- Equation (9), for every nonpositive canonical western frame. -/
theorem negative_w (E : OpenSquare) (data : Data E) (d r : ℝ)
    (dp : 0<d) (rn : 0≤r) (order : r≤d) :
    lower E d (-r)<(13/50)*r := by
  let k := E.c*d-E.s*r
  let h := E.s*d+E.c*r
  have cp : 0<E.c := by linarith only [data.cosine]
  have kp : 0<k := by
    have first := mul_pos dp (show 0<E.c-E.s by linarith only [data.cosine,data.sineUpper])
    have last := mul_nonneg data.sine.le (sub_nonneg.mpr order)
    dsimp [k]
    nlinarith only [first,last]
  have hp : 0<h := add_pos_of_pos_of_nonneg (mul_pos data.sine dp) (mul_nonneg cp.le rn)
  have formula := C1092WholeSupports.lower_pn E d (-r) k (-h)
    (by dsimp [k]; ring) (by dsimp [h]; ring) kp.le (by linarith only [hp])
  have first := mul_lt_mul_of_pos_left data.lowerU kp
  have last := mul_lt_mul_of_pos_left data.upperV hp
  have bound : lower E d (-r)<k*(E.c-1)+(13/50)*E.s*h := by
    rw [formula]
    nlinarith only [first,last]
  have signs := coefficients E data
  have negative := add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg dp signs.1)
    (mul_nonpos_of_nonneg_of_nonpos rn signs.2.1.le)
  have identity : k*(E.c-1)+(13/50)*E.s*h-(13/50)*r=
      d*((1-E.c)*(13/50-(37/50)*E.c))+
        r*(E.s-(37/50)*E.c*E.s-13/50) := by
    dsimp [k,h]
    linear_combination (13/50)*d*E.unit_normal
  linarith only [bound,identity,negative]

/-- Both relative-angle orders for the positive western longitudinal
normal, including the zero determinant shared by the two formulas. -/
theorem positive_u (E : OpenSquare) (data : Data E) (d r : ℝ)
    (dp : 0<d) (rn : 0≤r) : lower E d r<0 := by
  let k := E.c*d+E.s*r
  let delta := E.c*r-E.s*d
  have cp : 0<E.c := by linarith only [data.cosine]
  have kp : 0<k := add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg data.sine.le rn)
  by_cases sign : 0≤delta
  · have formula := C1092WholeSupports.lower_nn E d r k delta
      (by dsimp [k]; ring) (by dsimp [delta]; ring) kp.le sign
    have first := mul_neg_of_pos_of_neg kp
      (show E.loU<0 by linarith only [data.lowerU,data.cosineUpper])
    have last := mul_nonpos_of_nonneg_of_nonpos sign
      (show E.loV≤0 by linarith only [data.lowerV,cp,data.sine])
    rw [formula]
    exact add_neg_of_neg_of_nonpos first last
  · have negativeDelta : delta≤0 := le_of_not_ge sign
    have formula := C1092WholeSupports.lower_pn E d r k delta
      (by dsimp [k]; ring) (by dsimp [delta]; ring) kp.le negativeDelta
    have first := mul_lt_mul_of_pos_left data.lowerU kp
    have last := mul_le_mul_of_nonpos_left data.upperV.le negativeDelta
    have bound : lower E d r<k*(E.c-1)-(13/50)*E.s*delta := by
      rw [formula]
      nlinarith only [first,last]
    have signs := coefficients E data
    have negative := add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg dp signs.1)
      (mul_nonpos_of_nonneg_of_nonpos rn signs.2.2.le)
    have identity : k*(E.c-1)-(13/50)*E.s*delta=
        d*((1-E.c)*(13/50-(37/50)*E.c))+r*(E.s*((37/50)*E.c-1)) := by
      dsimp [k,delta]
      linear_combination (13/50)*d*E.unit_normal
    linarith only [bound,identity,negative]

/-- Equations (11)--(12), covering the remaining positive western normal
over both complete relative-angle intervals. -/
theorem positive_v (E : OpenSquare) (data : Data E) (d r : ℝ)
    (dp : 0<d) (rn : 0≤r) (order : r≤d) :
    lower E r (-d)<(13/50)*d := by
  let k := E.c*d+E.s*r
  let delta := E.c*r-E.s*d
  have cp : 0<E.c := by linarith only [data.cosine]
  have kp : 0<k := add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg data.sine.le rn)
  by_cases sign : delta≤0
  · have uSign : r*E.c+(-d)*E.s≤0 := by dsimp [delta] at sign; nlinarith only [sign]
    have vSign : -r*E.s+(-d)*E.c≤0 := by dsimp [k] at kp; nlinarith only [kp]
    have formula : lower E r (-d)=delta*(E.loU+E.side)-k*(E.loV+E.side) := by
      rw [SupportBands.lower_nn E r (-d) uSign vSign]
      dsimp [delta,k]
      ring
    have first := mul_le_mul_of_nonpos_left data.upperU.le sign
    have last := mul_lt_mul_of_pos_left data.upperV kp
    have bound : lower E r (-d)<(13/50)*E.c*delta+(13/50)*E.s*k := by
      rw [formula]
      nlinarith only [first,last]
    have identity : (13/50)*E.c*delta+(13/50)*E.s*k=(13/50)*r := by
      dsimp [delta,k]
      linear_combination (13/50)*r*E.unit_normal
    rw [identity] at bound
    linarith only [bound,order]
  · have positiveDelta : 0≤delta := (le_of_not_ge sign)
    have formula := C1092WholeSupports.lower_pn E r (-d) delta (-k)
      (by dsimp [delta]; ring) (by dsimp [k]; ring) positiveDelta (by linarith only [kp])
    have first := mul_le_mul_of_nonneg_left data.lowerU.le positiveDelta
    have last := mul_lt_mul_of_pos_left data.upperV kp
    have bound : lower E r (-d)<delta*(E.c-1)+(13/50)*E.s*k := by
      rw [formula]
      nlinarith only [first,last]
    have signs := coefficients E data
    have negative := add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos rn signs.1.le) (mul_neg_of_pos_of_neg dp signs.2.1)
    have identity : delta*(E.c-1)+(13/50)*E.s*k-(13/50)*d=
        r*((1-E.c)*(13/50-(37/50)*E.c))+
          d*(E.s-(37/50)*E.c*E.s-13/50) := by
      dsimp [delta,k]
      linear_combination (13/50)*r*E.unit_normal
    linarith only [bound,identity,negative]

#print axioms negative_w
#print axioms positive_u
#print axioms positive_v
end N12Compact.Completion.OtherCases.C983.F4SoutheastSignSupports
