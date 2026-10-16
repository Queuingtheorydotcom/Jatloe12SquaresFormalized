import Compact.Completion.C981.Crosspoint
import Compact.Completion.C1092.MixedSpan
import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OutwardPoint
import Compact.Completion.OtherCases.C1089.WallOrigins
import Compact.Completion.OtherCases.InnerCornerObstruction.Main

/-! C1089-MMMP-SINGLETON-ENDING, from the literal actual-owner core.
The singleton supplies its real horizontal interval. Its inner corner is
never assumed owned, and the absent original marker is only an exclusion.
The preceding wall-sign/core entrance remains a separate obligation. This
module derives the ordinary southwest pair and every geometric consequence
used in the final duplicate. It is uncompiled source, not ExcludesCase1089. -/
namespace N12Compact.Completion.OtherCases.C1089.MMMPSingletonEnding
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  topContained : InsideContainer (q 11)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  absentMarker : ¬(q 4).Inside (457/500) 1
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF : (q 4).Inside 1 (87/50) ∨
    (q 4).Inside (8/5) 1 ∨ (q 4).Inside 2 (87/50)
  southwestG : (q 4).Inside 1 (8/5) ∨
    (q 4).Inside (87/50) 1 ∨ (q 4).Inside (87/50) 2
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastG7 : (q 6).Inside (113/50) 3
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF5 : (q 7).Inside 2 (113/50)
  northwestG3 : (q 7).Inside (87/50) 2
  leftMarker : (q 8).Inside (457/500) 2
  topMarker : (q 11).Inside 2 (1543/500)
  topF3 : (q 11).Inside (8/5) 3

theorem singleton_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (q 0).Inside x 1 := by
  let t := (50/31)*(x-28/25)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 0) (28/25) 1 (87/50) 1 t
    h.singletonNear h.singletonFar tn tu using 1 <;> dsimp only [t] <;> ring

/-- The covering alternatives, mixed-span obstruction and actual foreign
owners force F0 and G0 into the ordinary southwest central. -/
theorem southwest_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside 1 (87/50) ∧ (q 4).Inside 1 (8/5) := by
  have g0 : (q 4).Inside 1 (8/5) := by
    rcases h.southwestG with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    · exact False.elim (h.apart 4 7 (by decide) _ _ ⟨own,h.northwestG3⟩)
  have f0 : (q 4).Inside 1 (87/50) := by
    by_contra missingF0
    have f4 : (q 4).Inside 2 (87/50) := by
      rcases h.southwestF with own | own | own
      · exact False.elim (missingF0 own)
      · exact False.elim (h.apart 4 0 (by decide) _ _
          ⟨own,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
      · exact own
    exact C1092MixedSpan.impossible (pullX (q 4)) (h.side 4)
      (by norm_num [inside_pullX]; exact f4)
      (by norm_num [inside_pullX]; exact g0)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 7 (by decide) _ _ ⟨own,h.northwestG3⟩)
      (by norm_num [inside_pullX]; exact missingF0)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 0 (by decide) _ _ ⟨own,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
  exact ⟨f0,g0⟩

/-- The top advance is proved from the genuine top wall; the two strict
top points in the rotated crosspoint theorem have this one actual owner. -/
theorem northwest_crosspoint (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (3/2) 2 := by
  have top := WallOrigins.top_left_advance q (h.side 11) h.topContained h.apart
    h.topMarker h.topF3 h.northeastG7 h.northwestMarker
  have middle : (q 11).Inside (3/2) 3 := by
    convert inside_segment (q 11) (36/25) 3 (8/5) 3 (3/8)
      top h.topF3 (by norm_num) (by norm_num) using 1 <;> norm_num
  have result := C981CompletionCrosspoint.point (pullSwap (pullX (q 7))) (h.side 7)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 7 11 (by decide) _ _ ⟨own,h.topF3⟩)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 7 11 (by decide) _ _ ⟨own,middle⟩)
  norm_num [inside_pullSwap,inside_pullX] at result
  exact result

/-- This is an omission by Q4, with no claim that the tested corner has
an owner. The marker, singleton interval, left marker and new crosspoint
remain four distinct actual reasons for exclusion. -/
theorem southwest_corner_excluded (q : Fin 12 → OpenSquare) (h : Input q) :
    ¬(q 4).Inside 1 1 :=
  InnerCornerObstruction.corner_excluded_original (q 4) (h.side 4) h.southwestMarker
    h.absentMarker
    (fun own => h.apart 4 0 (by decide) _ _ ⟨own,h.singletonNear⟩)
    (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    (fun own => h.apart 4 7 (by decide) _ _ ⟨own,northwest_crosspoint q h⟩)

theorem northwest_duplicate (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (77/50) (201/100) := by
  have result := CommonCases.InwardPoint.point_original (pullY (pullX (q 7))) (h.side 7)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 7 11 (by decide) _ _ ⟨own,h.topF3⟩)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

/-- The arbitrary-orientation outward theorem derives its sign lock from
the actual singleton interval; no orientation is supplied as a premise. -/
theorem southwest_duplicate (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside (77/50) (201/100) := by
  obtain ⟨f0,g0⟩ := southwest_pair q h
  have result := CommonCases.OutwardPoint.point_original (pullY (pullX (q 4))) (h.side 4)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact f0)
    (by norm_num [inside_pullY,inside_pullX]; exact g0)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 7 (by decide) _ _ ⟨own,h.northwestG3⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
      h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    (by norm_num [inside_pullY,inside_pullX]; exact southwest_corner_excluded q h)
    (by norm_num [inside_pullY,inside_pullX]; exact h.absentMarker)
    (by
      intro z low high own
      have actual := (inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp own)
      norm_num at actual
      exact h.apart 4 0 (by decide) _ _
        ⟨actual,singleton_bar q h (4-z) (by linarith only [high]) (by linarith only [low])⟩)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False :=
  h.apart 4 7 (by decide) _ _ ⟨southwest_duplicate q h,northwest_duplicate q h⟩

#print axioms southwest_pair
#print axioms northwest_crosspoint
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.MMMPSingletonEnding
