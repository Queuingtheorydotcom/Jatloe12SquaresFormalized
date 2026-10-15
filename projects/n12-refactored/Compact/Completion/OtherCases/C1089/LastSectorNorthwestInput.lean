import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OutwardPoint
import Compact.Completion.OtherCases.ShortDuplicatePoints
import Compact.Completion.OtherCases.InnerCornerObstruction.Inward
import Compact.Completion.OtherCases.InnerCornerObstruction.Main

/-! The actual inputs and common outward consequences for sections 4--5
of C1089-LAST-SECTOR-REDUCTION. The Q0 interval is horizontal; its omitted
original marker is not assigned an owner. No singleton inner corner or
canonical angle is assumed. Written source, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  absentMarker : ¬(q 4).Inside (457/500) 1
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF0 : (q 4).Inside 1 (87/50)
  southwestG0 : (q 4).Inside 1 (8/5)
  southeastSouth : (q 5).Inside 2 (3/2)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF : (q 7).Inside 1 (113/50) ∨
    (q 7).Inside (8/5) 3 ∨ (q 7).Inside 2 (113/50)
  northwestG : (q 7).Inside 1 (12/5) ∨
    (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3
  leftMarker : (q 8).Inside (457/500) 2
  leftF1 : (q 8).Inside 1 (113/50)
  leftG1 : (q 8).Inside 1 (12/5)
  topMarker : (q 11).Inside 2 (1543/500)

theorem singleton_bar (q : Fin 12 → OpenSquare) (h : Input q)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (q 0).Inside x 1 := by
  let t := (50/31)*(x-28/25)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 0) (28/25) 1 (87/50) 1 t
    h.singletonNear h.singletonFar tn tu using 1 <;> dsimp only [t] <;> ring

theorem f_alternatives (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (8/5) 3 ∨ (q 7).Inside 2 (113/50) := by
  rcases h.northwestF with own | own | own
  · exact False.elim (h.apart 7 8 (by decide) _ _ ⟨own,h.leftF1⟩)
  · exact Or.inl own
  · exact Or.inr own

theorem g_alternatives (q : Fin 12 → OpenSquare) (h : Input q) :
    (q 7).Inside (87/50) 2 ∨ (q 7).Inside (87/50) 3 := by
  rcases h.northwestG with own | own | own
  · exact False.elim (h.apart 7 8 (by decide) _ _ ⟨own,h.leftG1⟩)
  · exact Or.inl own
  · exact Or.inr own

/-- The three common outward points of section 3. The short middle point
is obtained by a triangle of the sharper bar point and the actual anchors. -/
theorem outward_points (q : Fin 12 → OpenSquare) (h : Input q)
    (missingCorner : ¬(q 4).Inside 1 1)
    (missingG3 : ¬(q 4).Inside (87/50) 2) :
    (q 4).Inside (77/50) (201/100) ∧
    (q 4).Inside (3/2) (51/25) ∧ (q 4).Inside (59/40) (17/8) := by
  let A := pullY (pullX (q 4))
  have chart (x y : ℝ) : A.Inside x y↔(q 4).Inside (4-x) (4-y) := by
    dsimp only [A]
    rw [inside_pullY,inside_pullX]
  have m : A.Inside (47/20) (47/20) := by norm_num [chart]; exact h.southwestMarker
  have f : A.Inside 3 (113/50) := by norm_num [chart]; exact h.southwestF0
  have g : A.Inside 3 (12/5) := by norm_num [chart]; exact h.southwestG0
  have d : ¬A.Inside (113/50) 2 := by norm_num [chart]; exact missingG3
  have r : ¬A.Inside (1543/500) 2 := by
    norm_num [chart]
    exact fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩
  have p : ¬A.Inside 3 3 := by norm_num [chart]; exact missingCorner
  have b : ¬A.Inside (1543/500) 3 := by norm_num [chart]; exact h.absentMarker
  have bar (z : ℝ) (low : 113/50≤z) (high : z≤14/5) : ¬A.Inside z 3 := by
    intro own
    have actual := (chart _ _).mp own
    norm_num only at actual
    exact h.apart 4 0 (by decide) _ _
      ⟨actual,singleton_bar q h (4-z) (by linarith only [high]) (by linarith only [low])⟩
  have first := CommonCases.OutwardPoint.point_original A (h.side 4) m f g d r p b bar
  have second := ShortDuplicatePoints.outward_of_bar A (h.side 4) m f g d r p b bar
  have third := OutwardBarPoint.point_original A (h.side 4) m f g d r p b bar
  norm_num [chart] at first second third
  exact ⟨first,second,third⟩

end N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest
