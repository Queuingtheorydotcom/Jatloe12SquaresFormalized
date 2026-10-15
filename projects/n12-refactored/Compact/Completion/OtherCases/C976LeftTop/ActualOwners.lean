import Compact.Completion.OtherCases.C976LeftTop.UpperPoints
import Compact.Completion.OtherCases.SouthwestSupportPoint.Main
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Geometry.WallUpperMissingReach
import Compact.Completion.C981.CornerAdvance

/-! C976-LEFT-UPPER-POINTS section 4 and the original Q8/Q11 application
of C976-LEFT-TOP-ANGLE. The indices below are the manuscript's actual
ascending-mask owners. All foreign segments stay in their single named
owner. The finite family/auxiliary entrance and the two southwest
crosspoint producers must still supply Data; no whole-case claim is made. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.ActualOwners
open S12 S12Pilot
set_option Elab.async false

structure Data (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  box : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singleton0First : (q 0).Inside (28/25) 1
  singleton0Last : (q 0).Inside (87/50) 1
  singleton1Low : (q 1).Inside 1 (8/5)
  singleton1Near : (q 1).Inside 1 (87/50)
  singleton1Seed : (q 1).Inside (19/25) (187/100)
  cornerMarker : (q 4).Inside 1 (1543/500)
  cornerPoint : (q 4).Inside 1 3
  southwestMarker : (q 5).Inside (33/20) (33/20)
  southwestF4 : (q 5).Inside 2 (87/50)
  southwestG3 : (q 5).Inside (87/50) 2
  southwestWest : (q 5).Inside (3/2) 2
  southwestSouth : (q 5).Inside 2 (3/2)
  southeastMarker : (q 6).Inside (47/20) (33/20)
  southeastG6 : (q 6).Inside (113/50) 2
  northeastG7 : (q 7).Inside (113/50) 3
  leftMarker : (q 8).Inside (457/500) 2
  northwestMarker : (q 8).Inside (33/20) (47/20)
  leftF1 : (q 8).Inside 1 (113/50)
  bottomOrigin : (q 9).Inside 2 1
  topMarker : (q 11).Inside 2 (1543/500)
  topF3 : (q 11).Inside (8/5) 3
  topG4 : (q 11).Inside (87/50) 3

theorem southwest_point (q : Fin 12 → OpenSquare) (h : Data q) :
    (q 5).Inside (127/100) (49/25) := by
  have bottomMiddle : (q 0).Inside (3/2) 1 := by
    convert inside_segment (q 0) (28/25) 1 (87/50) 1 (19/31)
      h.singleton0First h.singleton0Last (by norm_num) (by norm_num) using 1 <;> norm_num
  exact SouthwestSupportPoint.point_of_neighbours (q 5) (q 0) (q 6) (h.side 5)
    h.southwestMarker h.southwestF4 h.southwestG3 h.southwestWest h.southwestSouth
    (fun own => h.apart 5 8 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (fun own => h.apart 5 9 (by decide) _ _ ⟨own,h.bottomOrigin⟩)
    (fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.singleton1Low⟩)
    (fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.singleton1Near⟩)
    bottomMiddle h.singleton0Last h.southeastMarker h.southeastG6
    (h.apart 5 0 (by decide)) (h.apart 5 6 (by decide))

theorem top_reach (q : Fin 12 → OpenSquare) (h : Data q) : (q 11).Inside (36/25) 3 := by
  let T := pullSwap (pullY (pullX (q 11)))
  have box := container_pullSwap _ (container_pullY _ (container_pullX _ (h.box 11)))
  have advance := WallUpperMissingReach.point T (h.side 11) box
    (by dsimp only [T]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact h.topMarker)
    (by dsimp only [T]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact h.topF3)
    (by
      dsimp only [T]
      norm_num only [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun own => h.apart 11 7 (by decide) _ _ ⟨own,h.northeastG7⟩)
    (by
      dsimp only [T]
      norm_num only [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun own => h.apart 11 8 (by decide) _ _ ⟨own,h.northwestMarker⟩)
  dsimp only [T] at advance
  norm_num only [inside_pullSwap,inside_pullY,inside_pullX] at advance
  exact advance

theorem left_input (q : Fin 12 → OpenSquare) (h : Data q) :
    UpperPoints.Input ((q 8).translated 1 2) := by
  have chart (x y : ℝ) : ((q 8).translated 1 2).Inside x y↔(q 8).Inside (1+x) (2+y) :=
    inside_translated_iff _ _ _ _ _
  have point := southwest_point q h
  have reach := top_reach q h
  refine {
    side := h.side 8
    left := (chart _ _).mpr (by convert h.leftMarker using 1 <;> norm_num)
    marker := (chart _ _).mpr (by convert h.northwestMarker using 1 <;> norm_num)
    inward := (chart _ _).mpr (by convert h.leftF1 using 1 <;> norm_num)
    middle := ?_
    corner := ?_
    lower := ?_
    top := ?_
    segment := ?_ }
  · intro own
    apply h.apart 8 5 (by decide) _ _ ⟨?_,h.southwestWest⟩
    convert (chart _ _).mp own using 1 <;> norm_num
  · intro own
    apply h.apart 8 4 (by decide) _ _ ⟨?_,h.cornerPoint⟩
    convert (chart _ _).mp own using 1 <;> norm_num
  · intro own
    apply h.apart 8 5 (by decide) _ _ ⟨?_,point⟩
    convert (chart _ _).mp own using 1 <;> norm_num
  · intro x low high own
    let t : ℝ := (10/3)*(x-11/25)
    have tn : 0≤t := by dsimp only [t]; linarith only [low]
    have tu : t≤1 := by dsimp only [t]; linarith only [high]
    have foreign : (q 11).Inside (1+x) 3 := by
      convert inside_segment (q 11) (36/25) 3 (87/50) 3 t reach h.topG4 tn tu using 1
      · dsimp only [t]; ring
      · ring
    apply h.apart 8 11 (by decide) _ _ ⟨?_,foreign⟩
    convert (chart _ _).mp own using 1 <;> norm_num
  · intro t low high own
    have foreign : (q 1).Inside (1+(-6/25+(6/25)*t))
        (2+(-13/100-(13/100)*t)) := by
      convert inside_segment (q 1) (19/25) (187/100) 1 (87/50) t
        h.singleton1Seed h.singleton1Near low high using 1 <;> ring
    exact h.apart 8 1 (by decide) _ _ ⟨(chart _ _).mp own,foreign⟩

theorem left_points (q : Fin 12 → OpenSquare) (h : Data q) :
    (q 8).Inside (5/4) 3 ∧ (q 8).Inside 1 (14/5) ∧ (q 8).Inside (32/25) 3 := by
  have result := UpperPoints.points ((q 8).translated 1 2) (left_input q h)
  norm_num only [inside_translated_iff] at result
  exact result

theorem top_origin (q : Fin 12 → OpenSquare) (h : Data q) : (q 11).Inside 2 3 := by
  have leftHigh := (left_points q h).2.1
  have foreign : (q 8).Inside 1 (5/2) := by
    convert inside_segment (q 8) 1 (113/50) 1 (14/5) (4/9)
      h.leftF1 leftHigh (by norm_num) (by norm_num) using 1 <;> norm_num
  have boxB := container_pullY (q 11) (h.box 11)
  have boxK := container_pullY (q 4) (h.box 4)
  have origin := WallProfile.boundary_origin (pullY (q 11)) (pullY (q 4)) (457/500) (8/5)
    (h.side 11) (h.same 11 4)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num only [inside_pullY]; exact h.topMarker)
    (by norm_num only [inside_pullY]; exact h.topF3)
    (by norm_num only [inside_pullY]; exact h.cornerMarker)
    (by norm_num only [inside_pullY]; exact h.cornerPoint)
    (by
      norm_num only [inside_pullY]
      exact fun own => h.apart 4 8 (by decide) _ _ ⟨own,foreign⟩)
    (by
      intro x y pair
      simp only [inside_pullY] at pair
      exact h.apart 4 11 (by decide) x (4-y) pair)
  norm_num only [inside_pullY] at origin
  exact origin

/-- The northwest consequence uses the available actual G4=(1.74,3),
so the existing corner theorem applies directly with its original .74
omission. No new foreign point or stronger corner input is needed. -/
theorem northwest_reach (q : Fin 12 → OpenSquare) (h : Data q) :
    (q 4).Inside 1 (18/5) := by
  let K := (pullSwap (pullX (q 4))).translated 3 3
  have chart (x y : ℝ) : K.Inside x y↔(q 4).Inside (1-y) (3+x) := by
    dsimp only [K]
    rw [inside_translated_iff,inside_pullSwap,inside_pullX]
    rw [show (4:ℝ)-(3+y)=1-y by ring]
  have missing := (left_points q h).2.1
  have point := C981CompletionCornerAdvance.point K (h.side 4)
    (by
      intro x y own
      have wall := (h.box 4 (1-y) (3+x) ((chart x y).mp own)).1
      linarith only [wall])
    ((chart _ _).mpr (by convert h.cornerPoint using 1 <;> norm_num))
    (by
      intro own
      apply h.apart 4 8 (by decide) _ _ ⟨?_,missing⟩
      convert (chart _ _).mp own using 1 <;> norm_num)
    (by
      intro own
      apply h.apart 4 11 (by decide) _ _ ⟨?_,h.topG4⟩
      convert (chart _ _).mp own using 1 <;> norm_num)
  have result := (chart _ _).mp point
  norm_num at result
  exact result

theorem steep_negative_top (q : Fin 12 → OpenSquare) (h : Data q)
    (cosine : 0<(q 11).c) (sine : (q 11).s≤0) : (2/3)*(q 11).c< -(q 11).s := by
  have reach := top_reach q h
  have origin := top_origin q h
  have top : TopInput ((q 11).translated 1 2) where
    anchor := by norm_num only [inside_translated_iff]; exact reach
    origin := by norm_num only [inside_translated_iff]; exact origin
    marker := by norm_num only [inside_translated_iff]; exact h.topMarker
    missing := by
      norm_num only [inside_translated_iff]
      exact fun own => h.apart 11 7 (by decide) _ _ ⟨own,h.northeastG7⟩
    wall := by
      intro x y own
      have bound := (h.box 11 (1+x) (2+y) ((inside_translated_iff _ _ _ _ _).mp own)).2.2.2
      linarith only [bound]
  exact UpperPoints.steep_negative ((q 8).translated 1 2) ((q 11).translated 1 2)
    (left_input q h) top cosine sine (h.same 8 11)
    (fun x y pair => h.apart 8 11 (by decide) (1+x) (2+y)
      ⟨(inside_translated_iff _ _ _ _ _).mp pair.1,(inside_translated_iff _ _ _ _ _).mp pair.2⟩)

#print axioms left_points
#print axioms northwest_reach
#print axioms steep_negative_top
end N12Compact.Completion.OtherCases.C976LeftTop.ActualOwners
