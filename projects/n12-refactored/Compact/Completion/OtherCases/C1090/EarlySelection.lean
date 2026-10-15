import Compact.Completion.OtherCases.C1090.EarlyGeometry
import Compact.Completion.OtherCases.C1090.NESelectionOwners
import Compact.Completion.OtherCases.C1089.WallOrigins
import Compact.Completion.C1092.MixedSpan
import Compact.Completion.C981.UpperPoint

/-! C1090-SIMPLIFIED-PROOF sections 4--6. The northeast selection,
ordinary northwest points and top origin are derived from the actual raw
owners. The sole top-component disjunction stays visible in Input; no
154-assignment enumeration or list completeness is asserted. The optional
top F5 is rejected using the existing upper-point theorem's exact value
2.62, which lies in the same strict top segment as the prose's 2.65.
Source only, not compiled. -/
namespace N12Compact.Completion.OtherCases.C1090.Early
open S12 S12Pilot
set_option Elab.async false

theorem selection_input (q : Fin 12 → OpenSquare) (h : Input q) :
    NESelectionOwners.Data q where
  side := h.side
  apart := h.apart
  southeastMarker := h.southeastMarker
  southeastF8 := h.southeastF8
  southeastG8 := southeast_g8 q h
  northeastMarker := h.northeastMarker
  northwestMarker := h.northwestMarker
  cornerPoint := h.southeastCorner
  cornerMarker := h.southeastCornerRight
  rightMarker := h.rightMarker
  rightF9 := h.rightF9
  rightG9 := h.rightG9
  bottomG5 := h.bottomG5
  bottomAdvance := (bottom_advance q h).1
  fCover := by
    rcases h.northeastFCover with own | own | own
    · exact Or.inl own
    · exact Or.inr own
    · exact False.elim (h.apart 6 10 (by decide) _ _ ⟨own,h.rightF9⟩)
  gCover := by
    rcases h.northeastGCover with own | own | own
    · exact Or.inl own
    · exact Or.inr own
    · exact False.elim (h.apart 6 10 (by decide) _ _ ⟨own,h.rightG9⟩)

theorem northeast_selection (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 6).Inside (113/50) 3 ∧ ((q 6).Inside (113/50) 2 → (q 6).Inside (12/5) 3) :=
  NESelectionOwners.selection q (selection_input q h)

theorem top_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 11).Inside (8/5) 3 ∧ (q 11).Inside (87/50) 3 := by
  rcases h.topComponent with own | pair
  · exact False.elim (h.apart 11 6 (by decide) _ _ ⟨own,(northeast_selection q h).1⟩)
  · exact pair

theorem northwest_pair (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside 1 (113/50) ∧ (q 7).Inside 1 (12/5) := by
  have top := top_pair q h
  have g1 : (q 7).Inside 1 (12/5) := by
    rcases h.northwestGCover with own | own | own
    · exact own
    · exact False.elim (h.apart 7 4 (by decide) _ _ ⟨own,h.southwestG3⟩)
    · exact False.elim (h.apart 7 11 (by decide) _ _ ⟨own,top.2⟩)
  have f1 : (q 7).Inside 1 (113/50) := by
    by_contra missing
    have f5 : (q 7).Inside 2 (113/50) := by
      rcases h.northwestFCover with own | own | own
      · exact False.elim (missing own)
      · exact False.elim (h.apart 7 11 (by decide) _ _ ⟨own,top.1⟩)
      · exact own
    exact C1092MixedSpan.impossible (pullY (pullX (q 7))) (h.side 7)
      (by norm_num [inside_pullY,inside_pullX]; exact f5)
      (by norm_num [inside_pullY,inside_pullX]; exact g1)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 4 (by decide) _ _ ⟨own,h.southwestG3⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact missing)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,top.2⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,top.1⟩)
  exact ⟨f1,g1⟩

theorem top_advance (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 11).Inside (36/25) 3 :=
  C1089.WallOrigins.top_left_advance q (h.side 11) (h.box 11) h.apart
    h.topMarker (top_pair q h).1 (northeast_selection q h).1 h.northwestMarker

theorem top_origin (q : Fin 12 → OpenSquare) (h : Input q) : (q 11).Inside 2 3 :=
  C1089.WallOrigins.top_origin_from_northwest q h.side h.same h.box h.apart
    h.northwestMarker (northwest_pair q h).1 (northwest_pair q h).2 h.southwestG3
    h.mergedMarker12 (top_pair q h).2 h.topMarker h.northwestCornerMarker h.northwestCorner

theorem top_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 36/25≤x) (high : x≤2) : (q 11).Inside x 3 := by
  let t := (25/14)*(x-36/25)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 11) (36/25) 3 2 3 t
    (top_advance q h) (top_origin q h) tn tu using 1 <;> dsimp only [t] <;> ring

/-- The optional F5 creates one real vertical segment in T. The full
upper-point theorem puts (2,2.62) strictly in E and that same segment. -/
theorem top_f5_excluded (q : Fin 12 → OpenSquare) (h : Input q) :
    ¬(q 11).Inside 2 (113/50) := by
  intro f5
  have vertical (y : ℝ) (low : 113/50≤y) (high : y≤1543/500) :
      (q 11).Inside 2 y := by
    let t := (500/413)*(y-113/50)
    have tn : 0≤t := by dsimp only [t]; linarith only [low]
    have tu : t≤1 := by dsimp only [t]; linarith only [high]
    convert inside_segment (q 11) 2 (113/50) 2 (1543/500) t
      f5 h.topMarker tn tu using 1 <;> dsimp only [t] <;> ring
  have own := C981CompletionUpperPoint.point (q 6) (h.side 6)
    h.northeastMarker (northeast_selection q h).1
    (fun own => h.apart 6 11 (by decide) _ _
      ⟨own,vertical _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 11 (by decide) _ _
      ⟨own,vertical _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 10 (by decide) _ _ ⟨own,h.rightG9⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun own => h.apart 6 10 (by decide) _ _ ⟨own,right_advance q h⟩)
  exact h.apart 6 11 (by decide) _ _ ⟨own,vertical _ (by norm_num) (by norm_num)⟩

/-- The established early geometry, retaining the original input table
and covers for subsequent structural eliminations. -/
structure PointTable (q : Fin 12 → OpenSquare) : Prop extends Input q where
  leftBar : ∀ y : ℝ,5/4≤y → y≤7/4 → (q 8).Inside 1 y
  bottomAdvance : (q 9).Inside (14/5) 1
  bottomBar : ∀ x : ℝ,113/50≤x → x≤14/5 → (q 9).Inside x 1
  rightAdvance : (q 10).Inside 3 (64/25)
  rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → (q 10).Inside 3 y
  southwestSouth : (q 4).Inside 2 (3/2)
  southwestWest : (q 4).Inside (3/2) 2
  southeastG8 : (q 5).Inside 3 (8/5)
  northeastG7 : (q 6).Inside (113/50) 3
  northeastG6F7 : (q 6).Inside (113/50) 2 → (q 6).Inside (12/5) 3
  northwestF1 : (q 7).Inside 1 (113/50)
  northwestG1 : (q 7).Inside 1 (12/5)
  topF3 : (q 11).Inside (8/5) 3
  topG4 : (q 11).Inside (87/50) 3
  topAdvance : (q 11).Inside (36/25) 3
  topOrigin : (q 11).Inside 2 3
  topBar : ∀ x : ℝ,36/25≤x → x≤2 → (q 11).Inside x 3
  missingTopF5 : ¬(q 11).Inside 2 (113/50)

theorem point_table (q : Fin 12 → OpenSquare) (h : Input q) : PointTable q where
  toInput := h
  leftBar := left_bar q h
  bottomAdvance := (bottom_advance q h).1
  bottomBar := (bottom_advance q h).2
  rightAdvance := right_advance q h
  rightBar := right_bar q h
  southwestSouth := southwest_south q h
  southwestWest := southwest_west q h
  southeastG8 := southeast_g8 q h
  northeastG7 := (northeast_selection q h).1
  northeastG6F7 := (northeast_selection q h).2
  northwestF1 := (northwest_pair q h).1
  northwestG1 := (northwest_pair q h).2
  topF3 := (top_pair q h).1
  topG4 := (top_pair q h).2
  topAdvance := top_advance q h
  topOrigin := top_origin q h
  topBar := top_bar q h
  missingTopF5 := top_f5_excluded q h

#print axioms northeast_selection
#print axioms northwest_pair
#print axioms top_f5_excluded
#print axioms point_table
end N12Compact.Completion.OtherCases.C1090.Early
