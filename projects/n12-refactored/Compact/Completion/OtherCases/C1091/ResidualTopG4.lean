import Compact.Completion.OtherCases.C1091.ResidualInput
import Compact.Completion.C981.LastCycle
import Compact.Completion.C1092.MixedSpan

/-! C1091-complete-proof §§4–7. Top G4 forces both northwest inner
points. The merged-marker seed then advances the actual left wall. The
complete last-cycle theorem consumes these points after one transpose;
it includes both signs, all weak contacts and the full diagonal segment. -/
namespace N12Compact.Completion.OtherCases.C1091.Residual
open S12 S12Pilot
set_option Elab.async false

theorem northwest_points (q : Fin 12 → OpenSquare) (h : Input q)
    (top : (q 11).Inside (87/50) 3) :
    (q 7).Inside (87/50) 2 ∧ (q 7).Inside 2 (113/50) := by
  have elbow : (q 7).Inside (87/50) 2 := by
    rcases h.northwestG with own | own
    · exact own
    · exact False.elim (h.foreign 7 11 (by decide) _ _ top own)
  refine ⟨elbow,?_⟩
  by_contra missing
  apply C1092MixedSpan.impossible (pullSwap (q 7)) (h.side 7)
  · simpa only [inside_pullSwap] using elbow
  · simpa only [inside_pullSwap] using h.northwestF3
  · simpa only [inside_pullSwap] using missing
  · simpa only [inside_pullSwap] using h.foreign 7 11 (by decide) _ _ top
  · simpa only [inside_pullSwap] using h.foreign 7 8 (by decide) _ _ h.leftF1
  · simpa only [inside_pullSwap] using h.foreign 7 8 (by decide) _ _ h.leftG1

theorem left_long_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (northwest : (q 7).Inside (87/50) 2) :
    ∀ y : ℝ,113/50≤y → y≤14/5 → (q 8).Inside 1 y := by
  apply MergedMarkerSeed.wall_bar (q 4) (q 0) (q 7) (q 8)
  exact {
    sideA := h.side 4
    sideL := h.side 8
    boxL := h.box 8
    mergedLeft := h.mergedLeft
    mergedCentral := h.mergedMarker
    mergedLow := h.mergedLow
    corner := h.cornerSW
    northwestG3 := northwest
    northwestMarker := h.northwestMarker
    wallMarker := h.leftMarker
    wallF1 := h.leftF1
    wallG1 := h.leftG1
    apartAK := h.apart 4 0 (by decide)
    apartAN := h.apart 4 7 (by decide)
    apartLA := h.apart 8 4 (by decide)
    apartLN := h.apart 8 7 (by decide) }

theorem top_g4_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (top : (q 11).Inside (87/50) 3) : False := by
  have northwest := northwest_points q h top
  have leftBar := left_long_bar q h northwest.1
  apply C981CompletionLastCycle.impossible
    (pullSwap (q 5)) (pullSwap (q 6)) (pullSwap (q 7)) (pullSwap (q 11))
    (h.side 5) (h.cap 5) (h.same 5 6) (h.same 5 7) (h.same 6 11)
  · intro x y own
    exact (h.box 11 y x ((inside_pullSwap _ _ _).mp own)).2.2.2
  · simpa only [inside_pullSwap] using h.center
  · simpa only [inside_pullSwap] using h.south
  · simpa only [inside_pullSwap] using h.east
  · simpa only [inside_pullSwap] using h.southeastMarker
  · simpa only [inside_pullSwap] using h.foreign 5 4 (by decide) _ _ h.mergedMarker
  · intro y lo hi
    simpa only [inside_pullSwap] using h.foreign 5 9 (by decide) _ _ (h.bottomBar y lo hi)
  · intro x lo hi
    simpa only [inside_pullSwap] using h.foreign 5 10 (by decide) _ _ (h.rightBar x lo hi)
  · simpa only [inside_pullSwap] using h.northeastMarker
  · simpa only [inside_pullSwap] using h.northeastF9
  · simpa only [inside_pullSwap] using h.northeastG9
  · simpa only [inside_pullSwap] using h.foreign 6 5 (by decide) _ _ h.southeast_cut
  · simpa only [inside_pullSwap] using h.foreign 6 10 (by decide) _ _
      (h.rightBar 2 (by norm_num) (by norm_num))
  · simpa only [inside_pullSwap] using h.foreign 6 11 (by decide) _ _ h.topF7
  · simpa only [inside_pullSwap] using h.foreign 6 2 (by decide) _ _ h.cornerNE
  · simpa only [inside_pullSwap] using h.foreign 6 10 (by decide) _ _ h.rightMarker
  · simpa only [inside_pullSwap] using h.northwestMarker
  · simpa only [inside_pullSwap] using northwest.1
  · simpa only [inside_pullSwap] using northwest.2
  · simpa only [inside_pullSwap] using h.foreign 7 11 (by decide) _ _ top
  · intro x lo hi
    simpa only [inside_pullSwap] using h.foreign 7 8 (by decide) _ _ (leftBar x lo hi)
  · simpa only [inside_pullSwap] using h.foreign 5 0 (by decide) _ _ h.singletonFar
  · simpa only [inside_pullSwap] using top
  · simpa only [inside_pullSwap] using h.topF7
  · simpa only [inside_pullSwap] using h.foreign 11 7 (by decide) _ _ h.northwestF3
  · intro x y own
    exact h.apart 5 6 (by decide) y x
      ⟨(inside_pullSwap _ _ _).mp own.1,(inside_pullSwap _ _ _).mp own.2⟩
  · intro x y own
    exact h.apart 5 7 (by decide) y x
      ⟨(inside_pullSwap _ _ _).mp own.1,(inside_pullSwap _ _ _).mp own.2⟩
  · intro x y own
    exact h.apart 6 11 (by decide) y x
      ⟨(inside_pullSwap _ _ _).mp own.1,(inside_pullSwap _ _ _).mp own.2⟩

#print axioms northwest_points
#print axioms left_long_bar
#print axioms top_g4_impossible
end N12Compact.Completion.OtherCases.C1091.Residual
