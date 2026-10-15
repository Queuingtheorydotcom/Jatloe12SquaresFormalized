import Compact.Completion.OtherCases.C1090.ResidualCentralPoints
import Compact.Completion.OtherCases.C1089.WallOrigins
import Compact.Completion.OtherCases.F4PointTransfers
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.TopOnlyLeftPoint
import Compact.Completion.OtherCases.SouthwestSupportPoint.Main
import Compact.Completion.OtherCases.OrdinaryLeftTop.ShallowTopPair

/-! Actual-owner producers for the residual ending in C1089-REVERSE-
CYCLIC-ENDING sections 5--6, also applicable to the C1090 residual table.
The northwest marker belongs to Q7. Q8 is used only for its own left
marker and strict left points; no global absence of marker 1 is asserted.
The finite entrance must still produce this raw table. No side upper bound,
wall-center sign, canonical angle, bottom origin or support point is assumed.
Source translation only; these declarations have not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1090.Residual
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  southeastCornerMarker : (q 1).Inside 3 (457/500)
  southeastCorner : (q 1).Inside 3 1
  northeastCorner : (q 2).Inside 3 3
  northwestCornerMarker : (q 3).Inside 1 (1543/500)
  northwestCorner : (q 3).Inside 1 3
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF4 : (q 4).Inside 2 (87/50)
  southwestG3 : (q 4).Inside (87/50) 2
  southwestWest : (q 4).Inside (3/2) 2
  southwestSouth : (q 4).Inside 2 (3/2)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF8 : (q 5).Inside 3 (87/50)
  southeastG6 : (q 5).Inside (113/50) 2
  southeastG8 : (q 5).Inside 3 (8/5)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastF7 : (q 6).Inside (12/5) 3
  northeastG7 : (q 6).Inside (113/50) 3
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF1 : (q 7).Inside 1 (113/50)
  northwestG1 : (q 7).Inside 1 (12/5)
  leftMarker : (q 8).Inside (457/500) 2
  leftF0 : (q 8).Inside 1 (87/50)
  leftG0 : (q 8).Inside 1 (8/5)
  bottomMarker : (q 9).Inside 2 (457/500)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  bottomAdvance : (q 9).Inside (14/5) 1
  rightF9 : (q 10).Inside 3 (113/50)
  rightAdvance : (q 10).Inside 3 (64/25)
  topMarker : (q 11).Inside 2 (1543/500)
  topF3 : (q 11).Inside (8/5) 3
  topG4 : (q 11).Inside (87/50) 3

theorem bottom_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 113/50≤x) (high : x≤14/5) : (q 9).Inside x 1 := by
  let t := (50/27)*(x-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 9) (113/50) 1 (14/5) 1 t
    h.bottomG5 h.bottomAdvance tn tu using 1 <;> dsimp only [t] <;> ring

theorem right_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (y : ℝ) (low : 113/50≤y) (high : y≤64/25) : (q 10).Inside 3 y := by
  let t := (10/3)*(y-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 10) 3 (113/50) 3 (64/25) t
    h.rightF9 h.rightAdvance tn tu using 1 <;> dsimp only [t] <;> ring

theorem top_advance (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 11).Inside (36/25) 3 :=
  C1089.WallOrigins.top_left_advance q (h.side 11) (h.box 11) h.apart
    h.topMarker h.topF3 h.northeastG7 h.northwestMarker

theorem top_origin (q : Fin 12 → OpenSquare) (h : Input q) : (q 11).Inside 2 3 :=
  C1089.WallOrigins.top_origin_from_northwest q h.side h.same h.box h.apart
    h.northwestMarker h.northwestF1 h.northwestG1 h.southwestG3 h.leftMarker
    h.topG4 h.topMarker h.northwestCornerMarker h.northwestCorner

/-- The horizontal crosspoint uses an already proved local transfer with
two genuine omissions: F4 belongs to A and the bottom midpoint to B. -/
theorem southeast_east (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside (5/2) 2 :=
  F4PointTransfers.horizontal_original (q 5) (h.side 5)
    h.southeastMarker h.southeastG6 h.southeastF8
    (fun own => h.apart 5 4 (by decide) _ _ ⟨own,h.southwestF4⟩)
    (fun own => h.apart 5 9 (by decide) _ _
      ⟨own,bottom_bar q h _ (by norm_num) (by norm_num)⟩)

theorem northeast_outer_sharp (q : Fin 12 → OpenSquare) (h : Input q)
    (missing : ¬(q 6).Inside 2 (113/50)) :
    (q 6).Inside (101/40) (17/8) :=
  UpperBarPoint.point_original (q 6) (h.side 6) h.northeastMarker h.northeastF7 missing
    (fun own => h.apart 6 11 (by decide) _ _ ⟨own,top_origin q h⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun y low high own => h.apart 6 10 (by decide) _ _ ⟨own,right_bar q h y low high⟩)

theorem northeast_mixed_sharp (q : Fin 12 → OpenSquare) (h : Input q)
    (mixed : (q 6).Inside 2 (113/50)) : (q 6).Inside (121/50) (54/25) := by
  have point := ResidualCentralPoints.mixed_point ((q 6).translated 2 2) (h.side 6)
    (by norm_num [inside_translated_iff]; exact h.northeastMarker)
    (by norm_num [inside_translated_iff]; exact mixed)
    (by norm_num [inside_translated_iff]; exact h.northeastG7)
    (by norm_num [inside_translated_iff]; exact fun own =>
      h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (by norm_num [inside_translated_iff]; exact fun own =>
      h.apart 6 11 (by decide) _ _ ⟨own,top_origin q h⟩)
    (by norm_num [inside_translated_iff]; exact fun own =>
      h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (by norm_num [inside_translated_iff]; exact fun own =>
      h.apart 6 10 (by decide) _ _ ⟨own,h.rightF9⟩)
  norm_num [inside_translated_iff] at point
  exact point

/-- The two alternatives are proved separately, with their own exact
sharp point. No right origin is smuggled into the southeast transfer. -/
theorem southeast_lower (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 5).Inside 3 (3/2) := by
  have transfer (a b : ℝ) (parameters : ResidualCentralPoints.Parameters a b)
      (foreign : (q 6).Inside (2+a) (2+b)) : (q 5).Inside 3 (3/2) := by
    have point := ResidualCentralPoints.southeast_point ((q 5).translated 2 2)
      a b parameters (h.side 5)
      (by norm_num [inside_translated_iff]; exact h.southeastMarker)
      (by norm_num [inside_translated_iff]; exact h.southeastG6)
      (by norm_num [inside_translated_iff]; exact h.southeastF8)
      (by norm_num [inside_translated_iff]; exact fun own =>
        h.apart 5 4 (by decide) _ _ ⟨own,h.southwestSouth⟩)
      (fun own => h.apart 5 6 (by decide) _ _
        ⟨(inside_translated_iff _ _ _ _ _).mp own,foreign⟩)
    norm_num [inside_translated_iff] at point
    exact point
  by_cases mixed : (q 6).Inside 2 (113/50)
  · apply transfer (21/50) (4/25) (by constructor <;> norm_num)
    convert northeast_mixed_sharp q h mixed using 1 <;> norm_num
  · apply transfer (21/40) (1/8) (by constructor <;> norm_num)
    convert northeast_outer_sharp q h mixed using 1 <;> norm_num

theorem bottom_origin (q : Fin 12 → OpenSquare) (h : Input q) : (q 9).Inside 2 1 := by
  have result := WallProfile.boundary_origin (pullX (q 9)) (pullX (q 1))
    (457/500) (8/5) (h.side 9) (h.same 9 1)
    (by
      intro x y own
      exact (h.box 9 _ _ ((inside_pullX _ _ _).mp own)).2.2.1)
    (by
      intro x y own
      have wall := h.box 1 _ _ ((inside_pullX _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],wall.2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullX]; exact h.bottomMarker)
    (by norm_num [inside_pullX]; exact h.bottomF6)
    (by norm_num [inside_pullX]; exact h.southeastCornerMarker)
    (by norm_num [inside_pullX]; exact h.southeastCorner)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact h.apart 1 5 (by decide) _ _ ⟨actual,southeast_lower q h⟩)
    (by
      intro x y own
      exact h.apart 1 9 (by decide) _ _
        ⟨(inside_pullX _ _ _).mp own.1,(inside_pullX _ _ _).mp own.2⟩)
  norm_num [inside_pullX] at result
  exact result

theorem southwest_support (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 4).Inside (127/100) (49/25) := by
  have singletonMiddle : (q 0).Inside (3/2) 1 := by
    convert inside_segment (q 0) (28/25) 1 (87/50) 1 (19/31)
      h.singletonNear h.singletonFar (by norm_num) (by norm_num) using 1 <;> norm_num
  exact SouthwestSupportPoint.point_of_neighbours (q 4) (q 0) (q 5) (h.side 4)
    h.southwestMarker h.southwestF4 h.southwestG3 h.southwestWest h.southwestSouth
    (fun own => h.apart 4 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (fun own => h.apart 4 9 (by decide) _ _ ⟨own,bottom_origin q h⟩)
    (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftG0⟩)
    (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftF0⟩)
    singletonMiddle h.singletonFar h.southeastMarker h.southeastG6
    (h.apart 4 0 (by decide)) (h.apart 4 5 (by decide))

/-- OrdinaryLeftTop's seven distinct absences are all furnished by their
actual owners. In particular the northwest marker is owned by this Q7. -/
theorem ordinary_input (q : Fin 12 → OpenSquare) (h : Input q) :
    OrdinaryLeftTop.Input ((q 7).translated 1 2) where
  side := h.side 7
  marker := by norm_num [inside_translated_iff]; exact h.northwestMarker
  anchor := by norm_num [inside_translated_iff]; exact h.northwestF1
  left := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 8 (by decide) _ _ ⟨own,h.leftMarker⟩
  middle := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 4 (by decide) _ _ ⟨own,h.southwestWest⟩
  far := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 4 (by decide) _ _ ⟨own,h.southwestG3⟩
  corner := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northwestCorner⟩
  lower := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 4 (by decide) _ _ ⟨own,southwest_support q h⟩
  topNear := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 11 (by decide) _ _ ⟨own,top_advance q h⟩
  topFar := by
    norm_num [inside_translated_iff]
    exact fun own => h.apart 7 11 (by decide) _ _ ⟨own,h.topG4⟩

theorem northwest_upper_points (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (32/25) 3 ∧ (q 7).Inside (7/5) 3 := by
  obtain ⟨r,_,inside,_,near,far⟩ := OrdinaryLeftTop.frame _ (ordinary_input q h)
  have a := (inside _ _).mp near
  have b := (inside _ _).mp far
  norm_num [inside_translated_iff] at a b
  exact ⟨a,b⟩

theorem top_input (q : Fin 12 → OpenSquare) (h : Input q)
    (W : OpenSquare) (inside : ∀ x y,W.Inside x y↔(q 11).Inside x y) :
    OrdinaryLeftTop.ShallowTop.TopInput (W.translated 1 2) := by
  have chart (x y : ℝ) : (W.translated 1 2).Inside x y↔(q 11).Inside (1+x) (2+y) :=
    (inside_translated_iff W 1 2 x y).trans (inside (1+x) (2+y))
  exact {
    anchor := (chart _ _).mpr (by convert top_advance q h using 1 <;> norm_num)
    origin := (chart _ _).mpr (by convert top_origin q h using 1 <;> norm_num)
    marker := (chart _ _).mpr (by convert h.topMarker using 1 <;> norm_num)
    missing := by
      intro own
      apply h.apart 11 6 (by decide) _ _ ⟨?_,h.northeastG7⟩
      convert (chart _ _).mp own using 1 <;> norm_num
    wall := by
      intro x y own
      have bound := (h.box 11 (1+x) (2+y) ((chart _ _).mp own)).2.2.2
      linarith only [bound] }

#print axioms southeast_lower
#print axioms bottom_origin
#print axioms southwest_support
#print axioms northwest_upper_points
end N12Compact.Completion.OtherCases.C1090.Residual
