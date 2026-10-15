import Compact.Geometry.ABTransverse
import Mathlib.Tactic.LinearCombination

/-! Exact support formulas for the whole original square. In particular
every occurrence of the two face values refers to the same physical square. -/
namespace N12Compact.C1092WholeSupports
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem formulas (Q : OpenSquare) (nx ny : ℝ) :
    lower Q nx ny=(nx*Q.c+ny*Q.s)*Q.loU+(-nx*Q.s+ny*Q.c)*Q.loV+
        Q.side*min (nx*Q.c+ny*Q.s) 0+Q.side*min (-nx*Q.s+ny*Q.c) 0 ∧
    upper Q nx ny=(nx*Q.c+ny*Q.s)*Q.loU+(-nx*Q.s+ny*Q.c)*Q.loV+
        Q.side*max (nx*Q.c+ny*Q.s) 0+Q.side*max (-nx*Q.s+ny*Q.c) 0 := by
  let d := nx*Q.c+ny*Q.s
  let e := -nx*Q.s+ny*Q.c
  have cu := (center_coordinates Q).1
  have cv := (center_coordinates Q).2
  have center : nx*centerX Q+ny*centerY Q=d*(Q.loU+Q.side/2)+e*(Q.loV+Q.side/2) := by
    dsimp [d,e]
    linear_combination (nx*Q.c+ny*Q.s)*cu+(-nx*Q.s+ny*Q.c)*cv-
      (nx*centerX Q+ny*centerY Q)*Q.unit_normal
  change lower Q nx ny=d*Q.loU+e*Q.loV+Q.side*min d 0+Q.side*min e 0 ∧
    upper Q nx ny=d*Q.loU+e*Q.loV+Q.side*max d 0+Q.side*max e 0
  dsimp [lower,upper,supportRadius]
  change nx*centerX Q+ny*centerY Q-Q.side/2*(|d|+|e|)=_ ∧
    nx*centerX Q+ny*centerY Q+Q.side/2*(|d|+|e|)=_
  rw [center]
  by_cases hd : 0 ≤ d <;> by_cases he : 0 ≤ e
  · simp only [abs_of_nonneg hd,abs_of_nonneg he,min_eq_right hd,min_eq_right he,
      max_eq_left hd,max_eq_left he,mul_zero,add_zero]
    constructor <;> ring
  · have hen : e ≤ 0 := (lt_of_not_ge he).le
    simp only [abs_of_nonneg hd,abs_of_nonpos hen,min_eq_right hd,min_eq_left hen,
      max_eq_left hd,max_eq_right hen,mul_zero,add_zero]
    constructor <;> ring
  · have hdn : d ≤ 0 := (lt_of_not_ge hd).le
    simp only [abs_of_nonpos hdn,abs_of_nonneg he,min_eq_left hdn,min_eq_right he,
      max_eq_right hdn,max_eq_left he,mul_zero,add_zero]
    constructor <;> ring
  · have hdn : d ≤ 0 := (lt_of_not_ge hd).le
    have hen : e ≤ 0 := (lt_of_not_ge he).le
    simp only [abs_of_nonpos hdn,abs_of_nonpos hen,min_eq_left hdn,min_eq_left hen,
      max_eq_right hdn,max_eq_right hen,mul_zero,add_zero]
    constructor <;> ring

theorem lower_nn (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0 ≤ d) (en : 0 ≤ e) : lower Q nx ny=d*Q.loU+e*Q.loV := by
  rw [(formulas Q nx ny).1,du,dv,min_eq_right dn,min_eq_right en]
  ring

theorem lower_np (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : d ≤ 0) (en : 0 ≤ e) : lower Q nx ny=d*(Q.loU+Q.side)+e*Q.loV := by
  rw [(formulas Q nx ny).1,du,dv,min_eq_left dn,min_eq_right en]
  ring

theorem lower_pn (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0 ≤ d) (en : e ≤ 0) : lower Q nx ny=d*Q.loU+e*(Q.loV+Q.side) := by
  rw [(formulas Q nx ny).1,du,dv,min_eq_right dn,min_eq_left en]
  ring

theorem upper_np (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : d ≤ 0) (en : 0 ≤ e) : upper Q nx ny=d*Q.loU+e*(Q.loV+Q.side) := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_right dn,max_eq_left en]
  ring

#print axioms formulas
end N12Compact.C1092WholeSupports
