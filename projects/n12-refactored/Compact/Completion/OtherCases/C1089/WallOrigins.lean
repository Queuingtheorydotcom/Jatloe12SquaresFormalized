import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint.Main
import Compact.Geometry.WallUpperMissingReach

/-! Actual-owner wall-origin applications in C1089-LAST-SECTOR-POINTS
section 1 and C1089-LAST-SECTOR-REDUCTION section 6. Each omitted corner
halfpoint has its indicated actual foreign owner. The arbitrary-orientation
corner profile and all separator cases are proved in BoundaryOrigin.
These source applications have not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.WallOrigins
open S12 S12Pilot
set_option Elab.async false

/-- The actual lower right wall supplies the corner exclusion needed to
force the bottom origin. No point of the southeast central is used here. -/
theorem bottom_origin (q : Fin 12 → OpenSquare)
    (side : 1<(q 9).side) (same : (q 9).side=(q 1).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (bottomMarker : (q 9).Inside 2 (457/500))
    (bottomInner : (q 9).Inside (12/5) 1)
    (cornerMarker : (q 1).Inside 3 (457/500))
    (cornerPoint : (q 1).Inside 3 1)
    (rightLow : (q 10).Inside 3 (36/25))
    (rightHigh : (q 10).Inside 3 (8/5)) :
    (q 9).Inside 2 1 := by
  have rightMiddle : (q 10).Inside 3 (3/2) := by
    convert inside_segment (q 10) 3 (36/25) 3 (8/5) (3/8)
      rightLow rightHigh (by norm_num) (by norm_num) using 1 <;> norm_num
  have result := WallProfile.boundary_origin (pullX (q 9)) (pullX (q 1))
    (457/500) (8/5) side same
    (by
      intro x y own
      exact (contained 9 _ _ ((inside_pullX _ _ _).mp own)).2.2.1)
    (by
      intro x y own
      have wall := contained 1 _ _ ((inside_pullX _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],wall.2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullX]; exact bottomMarker)
    (by norm_num [inside_pullX]; exact bottomInner)
    (by norm_num [inside_pullX]; exact cornerMarker)
    (by norm_num [inside_pullX]; exact cornerPoint)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact apart 1 10 (by decide) _ _ ⟨actual,rightMiddle⟩)
    (by
      intro x y own
      exact apart 1 9 (by decide) _ _
        ⟨(inside_pullX _ _ _).mp own.1,(inside_pullX _ _ _).mp own.2⟩)
  norm_num [inside_pullX] at result
  exact result

/-- The top-origin transfer uses the actual paired northeast corner and
its halfpoint exclusion in the northeast central. All wall contacts are weak. -/
theorem top_origin (q : Fin 12 → OpenSquare)
    (side : 1<(q 11).side) (same : (q 11).side=(q 2).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (topMarker : (q 11).Inside 2 (1543/500))
    (topInner : (q 11).Inside (12/5) 3)
    (cornerMarker : (q 2).Inside 3 (1543/500))
    (cornerPoint : (q 2).Inside 3 3)
    (northeastHalf : (q 6).Inside 3 (5/2)) :
    (q 11).Inside 2 3 := by
  have chart (i : Fin 12) (x y : ℝ) :
      (pullY (pullX (q i))).Inside x y ↔ (q i).Inside (4-x) (4-y) := by
    rw [inside_pullY,inside_pullX]
  have result := WallProfile.boundary_origin (pullY (pullX (q 11)))
    (pullY (pullX (q 2))) (457/500) (8/5) side same
    (by
      intro x y own
      have wall := contained 11 _ _ ((chart _ _ _).mp own)
      linarith only [wall.2.2.2])
    (by
      intro x y own
      have wall := contained 2 _ _ ((chart _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],by linarith only [wall.2.2.2]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [chart]; exact topMarker)
    (by norm_num [chart]; exact topInner)
    (by norm_num [chart]; exact cornerMarker)
    (by norm_num [chart]; exact cornerPoint)
    (by
      intro own
      have actual := (chart _ _ _).mp own
      norm_num at actual
      exact apart 2 6 (by decide) _ _ ⟨actual,northeastHalf⟩)
    (by
      intro x y own
      exact apart 2 11 (by decide) _ _
        ⟨(chart _ _ _).mp own.1,(chart _ _ _).mp own.2⟩)
  have actual := (chart _ _ _).mp result
  norm_num at actual
  exact actual

/-- The complete original top-origin application: the ordinary northeast
halfpoint is derived from its marker and four actual foreign sources. -/
theorem top_origin_of_ordinary (q : Fin 12 → OpenSquare)
    (side : ∀ i,1<(q i).side) (same : ∀ i j,(q i).side=(q j).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (northeastMarker : (q 6).Inside (47/20) (47/20))
    (northeastNear : (q 6).Inside 3 (113/50))
    (northeastFar : (q 6).Inside 3 (12/5))
    (southeastInward : (q 5).Inside (113/50) 2)
    (rightMarker : (q 10).Inside (1543/500) 2)
    (topNear : (q 11).Inside (113/50) 3)
    (topMarker : (q 11).Inside 2 (1543/500))
    (topInner : (q 11).Inside (12/5) 3)
    (cornerMarker : (q 2).Inside 3 (1543/500))
    (cornerPoint : (q 2).Inside 3 3) : (q 11).Inside 2 3 := by
  have half := OrdinaryMarkerHalfpoint.northeast_halfpoint (q 6) (side 6)
    northeastMarker northeastNear northeastFar
    (fun own => apart 6 5 (by decide) _ _ ⟨own,southeastInward⟩)
    (fun own => apart 6 10 (by decide) _ _ ⟨own,rightMarker⟩)
    (fun own => apart 6 2 (by decide) _ _ ⟨own,cornerPoint⟩)
    (fun own => apart 6 11 (by decide) _ _ ⟨own,topNear⟩)
  exact top_origin q (side 11) (same 11 2) contained apart
    topMarker topInner cornerMarker cornerPoint half

/-- The genuine top wall, F7 and two separate foreign points force the
top advance. Its proof does not require the top origin. -/
theorem top_advance (q : Fin 12 → OpenSquare)
    (side : 1<(q 11).side) (contained : InsideContainer (q 11))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (topMarker : (q 11).Inside 2 (1543/500))
    (topInner : (q 11).Inside (12/5) 3)
    (northwestNear : (q 7).Inside (87/50) 3)
    (northeastMarker : (q 6).Inside (47/20) (47/20)) :
    (q 11).Inside (64/25) 3 := by
  let T := pullSwap (pullY (q 11))
  have box := container_pullSwap _ (container_pullY _ contained)
  have result := WallUpperMissingReach.point T side box
    (by dsimp only [T]; norm_num [inside_pullSwap,inside_pullY]; exact topMarker)
    (by dsimp only [T]; norm_num [inside_pullSwap,inside_pullY]; exact topInner)
    (by
      dsimp only [T]
      norm_num [inside_pullSwap,inside_pullY]
      exact fun own => apart 11 7 (by decide) _ _ ⟨own,northwestNear⟩)
    (by
      dsimp only [T]
      norm_num [inside_pullSwap,inside_pullY]
      exact fun own => apart 11 6 (by decide) _ _ ⟨own,northeastMarker⟩)
  dsimp only [T] at result
  norm_num [inside_pullSwap,inside_pullY] at result
  exact result

/-- The actual left wall advance uses the ordinary southwest auxiliary
and the northwest marker as two separate foreign points. -/
theorem left_advance (q : Fin 12 → OpenSquare)
    (side : 1<(q 8).side) (contained : InsideContainer (q 8))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (leftMarker : (q 8).Inside (457/500) 2)
    (leftFar : (q 8).Inside 1 (12/5))
    (southwestNear : (q 4).Inside 1 (87/50))
    (northwestMarker : (q 7).Inside (33/20) (47/20)) :
    (q 8).Inside 1 (64/25) :=
  WallUpperMissingReach.point (q 8) side contained leftMarker leftFar
    (fun own => apart 8 4 (by decide) _ _ ⟨own,southwestNear⟩)
    (fun own => apart 8 7 (by decide) _ _ ⟨own,northwestMarker⟩)

/-- The same wall theorem after a physical half-turn. The real right
wall gives the lower point used by the bottom-origin transfer. -/
theorem right_low (q : Fin 12 → OpenSquare)
    (side : 1<(q 10).side) (contained : InsideContainer (q 10))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (rightMarker : (q 10).Inside (1543/500) 2)
    (rightFar : (q 10).Inside 3 (8/5))
    (northeastNear : (q 6).Inside 3 (113/50))
    (southeastMarker : (q 5).Inside (47/20) (33/20)) :
    (q 10).Inside 3 (36/25) := by
  let R := pullY (pullX (q 10))
  have box := container_pullY _ (container_pullX _ contained)
  have result := WallUpperMissingReach.point R side box
    (by dsimp only [R]; norm_num [inside_pullY,inside_pullX]; exact rightMarker)
    (by dsimp only [R]; norm_num [inside_pullY,inside_pullX]; exact rightFar)
    (by
      dsimp only [R]
      norm_num [inside_pullY,inside_pullX]
      exact fun own => apart 10 6 (by decide) _ _ ⟨own,northeastNear⟩)
    (by
      dsimp only [R]
      norm_num [inside_pullY,inside_pullX]
      exact fun own => apart 10 5 (by decide) _ _ ⟨own,southeastMarker⟩)
  dsimp only [R] at result
  norm_num [inside_pullY,inside_pullX] at result
  exact result

/-- The complementary top advance, from the actual leftward top pair.
This is also the top bar used by C1090, independently of its marker family. -/
theorem top_left_advance (q : Fin 12 → OpenSquare)
    (side : 1<(q 11).side) (contained : InsideContainer (q 11))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (topMarker : (q 11).Inside 2 (1543/500))
    (topFar : (q 11).Inside (8/5) 3)
    (northeastNear : (q 6).Inside (113/50) 3)
    (northwestMarker : (q 7).Inside (33/20) (47/20)) :
    (q 11).Inside (36/25) 3 := by
  let T := pullSwap (pullY (pullX (q 11)))
  have box := container_pullSwap _ (container_pullY _ (container_pullX _ contained))
  have result := WallUpperMissingReach.point T side box
    (by dsimp only [T]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact topMarker)
    (by dsimp only [T]; norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact topFar)
    (by
      dsimp only [T]
      norm_num [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun own => apart 11 6 (by decide) _ _ ⟨own,northeastNear⟩)
    (by
      dsimp only [T]
      norm_num [inside_pullSwap,inside_pullY,inside_pullX]
      exact fun own => apart 11 7 (by decide) _ _ ⟨own,northwestMarker⟩)
  dsimp only [T] at result
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at result
  exact result

/-- The other actual top-origin application, from the northwest ordinary
halfpoint. It retains Q3 as the corner and Q7 as the foreign halfpoint owner. -/
theorem top_origin_from_northwest (q : Fin 12 → OpenSquare)
    (side : ∀ i,1<(q i).side) (same : ∀ i j,(q i).side=(q j).side)
    (contained : ∀ i,InsideContainer (q i))
    (apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y))
    (northwestMarker : (q 7).Inside (33/20) (47/20))
    (northwestNear : (q 7).Inside 1 (113/50))
    (northwestFar : (q 7).Inside 1 (12/5))
    (southwestInward : (q 4).Inside (87/50) 2)
    (leftMarker : (q 8).Inside (457/500) 2)
    (topNear : (q 11).Inside (87/50) 3)
    (topMarker : (q 11).Inside 2 (1543/500))
    (cornerMarker : (q 3).Inside 1 (1543/500))
    (cornerPoint : (q 3).Inside 1 3) : (q 11).Inside 2 3 := by
  have half := OrdinaryMarkerHalfpoint.northwest_halfpoint (q 7) (side 7)
    northwestMarker northwestNear northwestFar
    (fun own => apart 7 4 (by decide) _ _ ⟨own,southwestInward⟩)
    (fun own => apart 7 8 (by decide) _ _ ⟨own,leftMarker⟩)
    (fun own => apart 7 3 (by decide) _ _ ⟨own,cornerPoint⟩)
    (fun own => apart 7 11 (by decide) _ _ ⟨own,topNear⟩)
  have result := WallProfile.boundary_origin (pullY (q 11)) (pullY (q 3))
    (457/500) (87/50) (side 11) (same 11 3)
    (by
      intro x y own
      have wall := contained 11 _ _ ((inside_pullY _ _ _).mp own)
      linarith only [wall.2.2.2])
    (by
      intro x y own
      have wall := contained 3 _ _ ((inside_pullY _ _ _).mp own)
      exact ⟨wall.1,by linarith only [wall.2.2.2]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullY]; exact topMarker)
    (by norm_num [inside_pullY]; exact topNear)
    (by norm_num [inside_pullY]; exact cornerMarker)
    (by norm_num [inside_pullY]; exact cornerPoint)
    (by
      intro own
      have actual := (inside_pullY _ _ _).mp own
      norm_num at actual
      exact apart 3 7 (by decide) _ _ ⟨actual,half⟩)
    (by
      intro x y own
      exact apart 3 11 (by decide) _ _
        ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [inside_pullY] at result
  exact result

#print axioms bottom_origin
#print axioms top_origin
#print axioms top_origin_of_ordinary
#print axioms top_advance
#print axioms left_advance
#print axioms right_low
#print axioms top_left_advance
#print axioms top_origin_from_northwest
end N12Compact.Completion.OtherCases.C1089.WallOrigins
