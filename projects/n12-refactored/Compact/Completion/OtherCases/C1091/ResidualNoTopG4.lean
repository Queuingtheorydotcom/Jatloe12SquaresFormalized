import Compact.Completion.OtherCases.C1091.ResidualInput
import Compact.Completion.C981.CommonCycle
import Compact.Geometry.WallUpperMissingReach

/-! C1091-complete-proof §3: the actual top owner omits G4. Its wall
advance supplies the two extra omissions in the complete common-cycle
theorem. Both physical squares are transposed; no owner is replaced. -/
namespace N12Compact.Completion.OtherCases.C1091.Residual
open S12 S12Pilot
set_option Elab.async false

theorem top_advance (q : Fin 12 → OpenSquare) (h : Input q)
    (missing : ¬(q 11).Inside (87/50) 3) : (q 11).Inside (64/25) 3 := by
  let W := pullSwap (pullY (q 11))
  have marker : W.Inside (457/500) 2 := by
    norm_num [W,inside_pullSwap,inside_pullY]
    exact h.topMarker
  have high : W.Inside 1 (12/5) := by
    norm_num [W,inside_pullSwap,inside_pullY]
    exact h.topF7
  have low : ¬W.Inside 1 (87/50) := by
    norm_num [W,inside_pullSwap,inside_pullY]
    exact missing
  have inward : ¬W.Inside (33/20) (47/20) := by
    norm_num [W,inside_pullSwap,inside_pullY]
    exact h.foreign 11 6 (by decide) _ _ h.northeastMarker
  have point := WallUpperMissingReach.point W (h.side 11)
    (container_pullSwap _ (container_pullY _ (h.box 11))) marker high low inward
  norm_num [W,inside_pullSwap,inside_pullY] at point
  exact point

theorem no_top_g4_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (missing : ¬(q 11).Inside (87/50) 3) : False := by
  have far := top_advance q h missing
  have mid : (q 11).Inside (5/2) 3 :=
    CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ h.topF7 far
      (by norm_num) (by norm_num) (by norm_num)
  apply C981CompletionCommonCycle.impossible (pullSwap (q 5)) (pullSwap (q 6))
    (h.side 5) (h.same 5 6)
  · simpa only [inside_pullSwap] using h.center
  · simpa only [inside_pullSwap] using h.south
  · simpa only [inside_pullSwap] using h.east
  · simpa only [inside_pullSwap] using h.southeastMarker
  · simpa only [inside_pullSwap] using h.foreign 5 4 (by decide) _ _ h.mergedMarker
  · intro y lo hi
    simpa only [inside_pullSwap] using h.foreign 5 9 (by decide) _ _ (h.bottomBar y lo hi)
  · simpa only [inside_pullSwap] using h.northeastMarker
  · simpa only [inside_pullSwap] using h.northeastF9
  · simpa only [inside_pullSwap] using h.northeastG9
  · simpa only [inside_pullSwap] using h.foreign 6 5 (by decide) _ _ h.southeast_cut
  · simpa only [inside_pullSwap] using h.foreign 6 10 (by decide) _ _
      (h.rightBar 2 (by norm_num) (by norm_num))
  · simpa only [inside_pullSwap] using h.foreign 6 11 (by decide) _ _ h.topF7
  · simpa only [inside_pullSwap] using h.foreign 6 2 (by decide) _ _ h.cornerNE
  · simpa only [inside_pullSwap] using h.foreign 6 11 (by decide) _ _ far
  · simpa only [inside_pullSwap] using h.foreign 6 11 (by decide) _ _ mid
  · simpa only [inside_pullSwap] using h.foreign 6 10 (by decide) _ _ h.rightMarker
  · intro x y own
    exact h.apart 5 6 (by decide) y x
      ⟨(inside_pullSwap _ _ _).mp own.1,(inside_pullSwap _ _ _).mp own.2⟩

#print axioms top_advance
#print axioms no_top_g4_impossible
end N12Compact.Completion.OtherCases.C1091.Residual
