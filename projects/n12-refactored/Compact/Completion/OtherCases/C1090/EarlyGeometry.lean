import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Completion.OtherCases.C1090.MergedLeftSeed
import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.C981.Crosspoint
import Compact.Geometry.WallUpperMissingReach

/-! C1090-SIMPLIFIED-PROOF sections 3--6, starting from the compulsory
strict points and literal local covers. The singleton's actual horizontal
and off-row seeds remain explicit prerequisites. The top component
consequence is an explicit finite disjunction, not an asserted catalogue
receipt. Marker 1 belongs to the real merged Q8. No wall-center or square
angle is assumed. Source translation only; no compilation is claimed. -/
namespace N12Compact.Completion.OtherCases.C1090.Early
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  singletonSeed : (q 0).Inside (187/100) (19/25)
  southeastCornerBottom : (q 1).Inside 3 (457/500)
  southeastCornerRight : (q 1).Inside (1543/500) 1
  southeastCorner : (q 1).Inside 3 1
  northeastCorner : (q 2).Inside 3 3
  northwestCornerMarker : (q 3).Inside 1 (1543/500)
  northwestCorner : (q 3).Inside 1 3
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF4 : (q 4).Inside 2 (87/50)
  southwestG3 : (q 4).Inside (87/50) 2
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF8 : (q 5).Inside 3 (87/50)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  mergedMarker1 : (q 8).Inside (457/500) 1
  mergedMarker12 : (q 8).Inside (457/500) 2
  bottomMarker : (q 9).Inside 2 (457/500)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  rightMarker : (q 10).Inside (1543/500) 2
  rightF9 : (q 10).Inside 3 (113/50)
  rightG9 : (q 10).Inside 3 (12/5)
  topMarker : (q 11).Inside 2 (1543/500)
  southeastGCover : (q 5).Inside (113/50) 1 ∨
    (q 5).Inside (113/50) 2 ∨ (q 5).Inside 3 (8/5)
  northeastFCover : (q 6).Inside 2 (113/50) ∨
    (q 6).Inside (12/5) 3 ∨ (q 6).Inside 3 (113/50)
  northeastGCover : (q 6).Inside (113/50) 2 ∨
    (q 6).Inside (113/50) 3 ∨ (q 6).Inside 3 (12/5)
  northwestFCover : (q 7).Inside 1 (113/50) ∨
    (q 7).Inside (8/5) 3 ∨ (q 7).Inside 2 (113/50)
  northwestGCover : (q 7).Inside 1 (12/5) ∨
    (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3
  /-- Finite component consequence still to be supplied by the entrance. -/
  topComponent : (q 11).Inside (113/50) 3 ∨
    ((q 11).Inside (8/5) 3 ∧ (q 11).Inside (87/50) 3)

theorem singleton_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (q 0).Inside x 1 := by
  let t := (50/31)*(x-28/25)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 0) (28/25) 1 (87/50) 1 t
    h.singletonNear h.singletonFar tn tu using 1 <;> dsimp only [t] <;> ring

theorem left_bar (q : Fin 12 → OpenSquare) (h : Input q) :
    ∀ y : ℝ,5/4≤y → y≤7/4 → (q 8).Inside 1 y :=
  MergedLeftSeed.actual_segment q (h.side 8) (h.box 8) h.mergedMarker1 h.mergedMarker12

theorem bottom_advance (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 9).Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (q 9).Inside x 1 :=
  (C1089.ContinuousBottom.reach (q 9) (h.side 9) (h.box 9)
    h.bottomMarker h.bottomF6 h.bottomG5
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonSeed⟩)
    (fun own => h.apart 9 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)).2

theorem right_advance (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 10).Inside 3 (64/25) := by
  have result := WallUpperMissingReach.point (pullX (q 10)) (h.side 10)
    (container_pullX _ (h.box 10))
    (by norm_num [inside_pullX]; exact h.rightMarker)
    (by norm_num [inside_pullX]; exact h.rightG9)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 10 5 (by decide) _ _ ⟨own,h.southeastF8⟩)
    (by norm_num [inside_pullX]; exact fun own =>
      h.apart 10 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
  norm_num [inside_pullX] at result
  exact result

theorem right_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (y : ℝ) (low : 113/50≤y) (high : y≤64/25) : (q 10).Inside 3 y := by
  let t := (10/3)*(y-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 10) 3 (113/50) 3 (64/25) t
    h.rightF9 (right_advance q h) tn tu using 1 <;> dsimp only [t] <;> ring

theorem southwest_south (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside 2 (3/2) := by
  have result := C981CompletionCrosspoint.point (pullY (pullX (q 4))) (h.side 4)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 8 (by decide) _ _ ⟨own,left_bar q h _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 8 (by decide) _ _ ⟨own,left_bar q h _ (by norm_num) (by norm_num)⟩)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

theorem southwest_west (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside (3/2) 2 := by
  have result := C981CompletionCrosspoint.point (pullSwap (pullY (pullX (q 4)))) (h.side 4)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 0 (by decide) _ _ ⟨own,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 0 (by decide) _ _ ⟨own,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at result
  exact result

theorem southeast_g8 (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside 3 (8/5) := by
  by_contra missing
  have elbow : (q 5).Inside (113/50) 2 := by
    rcases h.southeastGCover with own | own | own
    · exact False.elim (h.apart 5 9 (by decide) _ _ ⟨own,h.bottomG5⟩)
    · exact own
    · exact False.elim (missing own)
  have duplicate := (ElbowPoint.points_original (q 5) (h.side 5)
    h.southeastMarker elbow h.southeastF8
    (fun own => h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩) missing
    (fun own => h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩)).1
  exact h.apart 4 5 (by decide) _ _ ⟨southwest_south q h,duplicate⟩

#print axioms bottom_advance
#print axioms southwest_south
#print axioms southwest_west
#print axioms southeast_g8
end N12Compact.Completion.OtherCases.C1090.Early
