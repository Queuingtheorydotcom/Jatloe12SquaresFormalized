import Compact.Cases.C868.ActualBars

/-! The actual top wall reaches left. The half-turn transports C16's
original off-row seed as well as its owned G7, so the full bar follows
from the same raw wall theorem as the lower bar. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false

theorem top_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (x : ℝ) (low : 6/5≤x) (high : x≤87/50) :
    (owner p 32768).Inside x 3 := by
  let W := pullX (pullY (owner p 32768))
  have wi (u v : ℝ) : W.Inside u v↔(owner p 32768).Inside (4-u) (4-v) := by
    simp only [W,inside_pullX,inside_pullY]
  have size : 1<W.side := by
    change 1<(owner p 32768).side
    rw [show (owner p 32768).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have separate (mask : Nat) (hm : mask∈family) (hne : 32768≠mask)
      (u v : ℝ) (point : (owner p mask).Inside (4-u) (4-v)) :
      ¬W.Inside u v := fun own =>
    apart p hf 32768 mask (by decide +kernel) hm hne _ _
      ⟨(wi u v).mp own,point⟩
  have result := Completion.OtherCases.C1089.ContinuousBottom.reach_of_far W size
    (container_pullX _ (container_pullY _ (p.contained _)))
    (by
      apply (wi _ _).mpr
      norm_num only
      simpa using seed_inside p hf 32768 (by decide +kernel)
        (2,1543/500) (by decide +kernel))
    (by
      apply (wi _ _).mpr
      norm_num only
      simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 6)
    (by
      apply separate 16 (by decide +kernel) (by decide +kernel)
      norm_num only
      simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 1)
    (by
      apply separate 16 (by decide +kernel) (by decide +kernel)
      norm_num only
      simpa using seed_inside p hf 16 (by decide +kernel)
        (213/100,81/25) (by decide +kernel))
    (by
      apply separate 3072 (by decide +kernel) (by decide +kernel)
      norm_num only
      simpa using seed_inside p hf 3072 (by decide +kernel)
        (33/20,47/20) (by decide +kernel))
  have actual := (wi (4-x) 1).mp
    (result.2.2 (4-x) (by linarith only [high]) (by linarith only [low]))
  convert actual using 1 <;> ring

#print axioms top_bar
end N12Compact.C868
