import Compact.Geometry.SegmentCorner
import S12.ShortCluster
import Mathlib.Tactic.LinearCombination

/-! A genuine horizontal foreign segment joining two different lower
face exits bounds the actual closed lower vertex, including tangency. -/
namespace N12Compact.Completion.OtherCases.LowerCornerSupport
open S12 S12Pilot
set_option Elab.async false

theorem horizontal (q : OpenSquare) (lo hi : ℝ) (gap : lo<hi)
    (firstU : q.c*lo-q.s≤q.loU)
    (firstV : q.loV< -q.s*lo-q.c ∧ -q.s*lo-q.c<q.loV+q.side)
    (lastU : q.loU<q.c*hi-q.s ∧ q.c*hi-q.s<q.loU+q.side)
    (lastV : -q.s*hi-q.c≤q.loV)
    (avoid : ∀ x : ℝ,lo≤x → x≤hi → ¬q.Inside x (-1)) :
    -1≤q.s*q.loU+q.c*q.loV := by
  have crossing := SegmentCorner.crossing_order q.loU (q.loU+q.side)
    (-(q.loV+q.side)) (-q.loV)
    (q.c*lo-q.s) (q.s*lo+q.c) (q.c*hi-q.s) (q.s*hi+q.c)
    firstU lastU.1 lastU.2
    (by linarith only [firstV.2]) (by linarith only [firstV.1])
    (by linarith only [lastV])
    (by
      intro z low high point
      let x := (1-z)*lo+z*hi
      have first := mul_nonneg low (sub_nonneg.mpr gap.le)
      have last := mul_nonneg (show 0≤1-z by linarith only [high]) (sub_nonneg.mpr gap.le)
      apply avoid x (by dsimp only [x]; nlinarith only [first])
        (by dsimp only [x]; nlinarith only [last])
      dsimp only [x]
      refine ⟨?_,?_,?_,?_⟩
      · nlinarith only [point.1]
      · nlinarith only [point.2.1]
      · nlinarith only [point.2.2.2]
      · nlinarith only [point.2.2.1])
  have identity :
      (-q.loV-(q.s*lo+q.c))*((q.c*hi-q.s)-(q.c*lo-q.s))-
        (q.loU-(q.c*lo-q.s))*((q.s*hi+q.c)-(q.s*lo+q.c)) =
      -(hi-lo)*(q.s*q.loU+q.c*q.loV+1) := by
    linear_combination -(hi-lo)*q.unit_normal
  have scaled : 0≤(hi-lo)*(q.s*q.loU+q.c*q.loV+1) := by
    nlinarith only [crossing,identity]
  have nonnegative := nonneg_of_mul_nonneg_right scaled (sub_pos.mpr gap)
  linarith only [nonnegative]

#print axioms horizontal
end N12Compact.Completion.OtherCases.LowerCornerSupport

