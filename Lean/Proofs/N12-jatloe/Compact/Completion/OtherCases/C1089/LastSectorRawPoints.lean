import Compact.Completion.C981.Crosspoint
import Compact.Completion.OtherCases.C1089.LastSectorNorthwest
import Compact.Completion.OtherCases.C1089.ContinuousActual
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Completion.OtherCases.C1089.SingletonCorner

/-! Earlier actual-point producers for the last C1089 sector. All
center/origin/crosspoint conclusions are derived from literal strict points.
The finite core/auxiliary entrance remains separate, as does the stronger
singleton-seed producer, required only when its corner is omitted.
The actual Q0 horizontal bar is never transposed in place. Source only. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  contained : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  absentMarker : ∀ i,¬(q i).Inside (457/500) 1
  singletonMarker : (q 0).Inside 1 (457/500)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  singletonOffRow : (q 0).Inside (187/100) (19/25)
  strongerSeeds : ¬(q 0).Inside 1 1 →
    (q 0).Inside (91/50) 1 ∧ (q 0).Inside (49/25) (19/25)
  southeastCornerMarker : (q 1).Inside 3 (457/500)
  southeastCornerEastMarker : (q 1).Inside (1543/500) 1
  southeastCorner : (q 1).Inside 3 1
  northeastCornerMarker : (q 2).Inside 3 (1543/500)
  northeastCorner : (q 2).Inside 3 3
  northwestCorner : (q 3).Inside 1 3
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF : (q 4).Inside 1 (87/50) ∨
    (q 4).Inside (8/5) 1 ∨ (q 4).Inside 2 (87/50)
  southwestG : (q 4).Inside 1 (8/5) ∨
    (q 4).Inside (87/50) 1 ∨ (q 4).Inside (87/50) 2
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF4 : (q 5).Inside 2 (87/50)
  southeastG6 : (q 5).Inside (113/50) 2
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastF9 : (q 6).Inside 3 (113/50)
  northeastG9 : (q 6).Inside 3 (12/5)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF : (q 7).Inside 1 (113/50) ∨
    (q 7).Inside (8/5) 3 ∨ (q 7).Inside 2 (113/50)
  northwestG : (q 7).Inside 1 (12/5) ∨
    (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3
  leftMarker : (q 8).Inside (457/500) 2
  leftF1 : (q 8).Inside 1 (113/50)
  leftG1 : (q 8).Inside 1 (12/5)
  bottomMarker : (q 9).Inside 2 (457/500)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  rightMarker : (q 10).Inside (1543/500) 2
  rightF8 : (q 10).Inside 3 (87/50)
  rightG8 : (q 10).Inside 3 (8/5)
  rightSign : centerY (q 10)≤2
  topMarker : (q 11).Inside 2 (1543/500)
  topF7 : (q 11).Inside (12/5) 3
  topG7 : (q 11).Inside (113/50) 3

theorem singleton_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (q 0).Inside x 1 := by
  let t := (50/31)*(x-28/25)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 0) (28/25) 1 (87/50) 1 t
    h.singletonNear h.singletonFar tn tu using 1 <;> dsimp only [t] <;> ring

theorem bottom_advance (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 9).Inside (14/5) 1 :=
  (ContinuousBottom.reach (q 9) (h.side 9) (h.contained 9)
    h.bottomMarker h.bottomF6 h.bottomG5
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    (fun own => h.apart 9 0 (by decide) _ _ ⟨own,h.singletonOffRow⟩)
    (fun own => h.apart 9 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)).2.1

theorem southeast_south (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside 2 (3/2) := by
  have low := WallOrigins.right_low q (h.side 10) (h.contained 10) h.apart
    h.rightMarker h.rightG8 h.northeastF9 h.southeastMarker
  have middle : (q 10).Inside 3 (3/2) := by
    convert inside_segment (q 10) 3 (36/25) 3 (8/5) (3/8)
      low h.rightG8 (by norm_num) (by norm_num) using 1 <;> norm_num
  have result := C981CompletionCrosspoint.point (pullY (q 5)) (h.side 5)
    (by norm_num [inside_pullY]; exact h.southeastF4)
    (by norm_num [inside_pullY]; exact h.southeastG6)
    (by norm_num [inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,h.rightG8⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,middle⟩)
  norm_num [inside_pullY] at result
  exact result

theorem southwest_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside 1 (87/50) ∧ (q 4).Inside 1 (8/5) := by
  have f0 : (q 4).Inside 1 (87/50) := by
    rcases h.southwestF with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _
        ⟨own,singleton_bar q h _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 4 5 (by decide) _ _ ⟨own,h.southeastF4⟩)
  have g0 : (q 4).Inside 1 (8/5) := by
    by_contra missingG0
    have g3 : (q 4).Inside (87/50) 2 := by
      rcases h.southwestG with own | own | own
      · exact False.elim (missingG0 own)
      · exact False.elim (h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
      · exact own
    have result := ElbowPoint.points_original (pullX (q 4)) (h.side 4)
      (by norm_num [inside_pullX]; exact h.southwestMarker)
      (by norm_num [inside_pullX]; exact g3)
      (by norm_num [inside_pullX]; exact f0)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullX]; exact missingG0)
      (by norm_num [inside_pullX]; exact fun own =>
        h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    norm_num [inside_pullX] at result
    exact h.apart 4 5 (by decide) _ _ ⟨result.1,southeast_south q h⟩
  exact ⟨f0,g0⟩

theorem northwest_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (8/5) 3 ∧ (q 7).Inside (87/50) 3 := by
  have a := southwest_pair q h
  exact LastSectorNorthwest.ordinary_pair q {
    side := h.side
    apart := h.apart
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    absentMarker := h.absentMarker 4
    southwestMarker := h.southwestMarker
    southwestF0 := a.1
    southwestG0 := a.2
    southeastSouth := southeast_south q h
    northeastMarker := h.northeastMarker
    northwestMarker := h.northwestMarker
    northwestF := h.northwestF
    northwestG := h.northwestG
    leftMarker := h.leftMarker
    leftF1 := h.leftF1
    leftG1 := h.leftG1
    topMarker := h.topMarker }

theorem southeast_east (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside (5/2) 2 := by
  have far : (q 9).Inside (5/2) 1 := by
    convert inside_segment (q 9) (12/5) 1 (14/5) 1 (1/4)
      h.bottomF6 (bottom_advance q h) (by norm_num) (by norm_num) using 1 <;> norm_num
  have result := C981CompletionCrosspoint.point (pullX (pullSwap (q 5))) (h.side 5)
    (by norm_num [inside_pullX,inside_pullSwap]; exact h.southeastG6)
    (by norm_num [inside_pullX,inside_pullSwap]; exact h.southeastF4)
    (by norm_num [inside_pullX,inside_pullSwap]; exact h.southeastMarker)
    (by norm_num [inside_pullX,inside_pullSwap]; exact fun own =>
      h.apart 5 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by norm_num [inside_pullX,inside_pullSwap]; exact fun own =>
      h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullX,inside_pullSwap]; exact fun own =>
      h.apart 5 9 (by decide) _ _ ⟨own,h.bottomF6⟩)
    (by norm_num [inside_pullX,inside_pullSwap]; exact fun own =>
      h.apart 5 9 (by decide) _ _ ⟨own,far⟩)
  norm_num [inside_pullX,inside_pullSwap] at result
  exact result

theorem southeast_center_and_right_origin (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside 2 2 ∧ (q 10).Inside 3 2 :=
  ContinuousActual.southeast q h.side h.same h.contained h.apart
    h.southeastMarker h.southeastF4 h.southeastG6 h.southwestMarker
    h.rightMarker h.rightF8 h.rightSign h.bottomMarker h.bottomF6 h.singletonFar
    h.southeastCornerEastMarker h.southeastCorner

/-- Only the missing-corner branch asks for the stronger singleton seeds.
All other point/origin producers use the unconditional original seeds. -/
theorem singleton_corner (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 0).Inside 1 1 := by
  by_contra missing
  obtain ⟨near,offRow⟩ := h.strongerSeeds missing
  exact missing (SingletonCorner.corner_of_seeds q h.side h.same h.contained h.apart
    h.singletonMarker near offRow h.southeastCornerMarker h.southeastCorner
    h.southeastMarker (southeast_south q h) h.northeastF9 h.bottomMarker h.bottomF6
    (bottom_advance q h) h.rightMarker h.rightG8)

#print axioms southwest_pair
#print axioms northwest_pair
#print axioms singleton_corner
end N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints
