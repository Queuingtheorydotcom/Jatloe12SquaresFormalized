import Compact.Cases.C898.ChordFusedData
import Compact.Cases.C898.ChordFusedNeighbors

/-! Direct original53-pose coverage into the existing49-pose exit.
The central square is index0; indices1,2,3 are the original left-window
neighbors0,7,11 and indices4,5,6 the right-window neighbors3,6,9. -/

namespace N12Compact.C898Chord.Fused
open S12 S12Pilot C898Shared AngleSection FourSquareAnchors

theorem chord_fused (q : Fin 7 → OpenSquare)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (cap : (q 0).side ≤ 1001/1000)
    (left : ClosedInside (q 0) (33/20) (33/20))
    (right : ClosedInside (q 0) (47/20) (33/20))
    (hs : OrientedPoseCovered continuousScout898Domain5_0 (q 0))
    (hn0 : OrientedPoseCovered continuousScout898Domain0_9 (q 1))
    (hn1 : OrientedPoseCovered continuousScout898Domain7_7 (q 2))
    (hn2 : OrientedPoseCovered continuousScout898Domain11_0 (q 3))
    (hn3 : OrientedPoseCovered continuousScout898Domain3_3 (q 4))
    (hn4 : OrientedPoseCovered continuousScout898Domain6_5 (q 5))
    (hn5 : OrientedPoseCovered continuousScout898Domain9_8 (q 6)) :
    OrientedPoseCovered continuousScout898Domain5_11 (q 0) := by
  let leftIndices : Fin 4 → Fin 7 := ![0,1,2,3]
  let rightIndices : Fin 4 → Fin 7 := ![0,4,5,6]
  let leftSquares : Fin 4 → OpenSquare := fun i => q (leftIndices i)
  let rightSquares : Fin 4 → OpenSquare := fun i => q (rightIndices i)
  have leftInjective : Function.Injective leftIndices := by decide +kernel
  have rightInjective : Function.Injective rightIndices := by decide +kernel
  have leftApart : ∀ i j, i ≠ j → ∀ x y,
      ¬ ((leftSquares i).Inside x y ∧ (leftSquares j).Inside x y) := by
    intro i j different
    exact hd _ _ (fun same => different (leftInjective same))
  have rightApart : ∀ i j, i ≠ j → ∀ x y,
      ¬ ((rightSquares i).Inside x y ∧ (rightSquares j).Inside x y) := by
    intro i j different
    exact hd _ _ (fun same => different (rightInjective same))
  have leftSections : ∀ x, (leftLo : ℝ) ≤ x → x ≤ (leftHi : ℝ) →
      ∀ i : Fin 3, VerticalSection (leftSquares i.succ) x := by
    intro x hx0 hx1 i
    fin_cases i
    · exact neighbor_cover_sound leftLo leftHi continuousScout898Domain0_9Ids
        LeftNeighbors.neighbors0 LeftNeighbors.neighbors0_covered
        LeftNeighbors.neighbors0_checked (q 1) (ha 1) hn0 x hx0 hx1
    · exact neighbor_cover_sound leftLo leftHi continuousScout898Domain7_7Ids
        LeftNeighbors.neighbors1 LeftNeighbors.neighbors1_covered
        LeftNeighbors.neighbors1_checked (q 2) (ha 2) hn1 x hx0 hx1
    · exact neighbor_cover_sound leftLo leftHi continuousScout898Domain11_0Ids
        LeftNeighbors.neighbors2 LeftNeighbors.neighbors2_covered
        LeftNeighbors.neighbors2_checked (q 3) (ha 3) hn2 x hx0 hx1
  have rightSections : ∀ x, (rightLo : ℝ) ≤ x → x ≤ (rightHi : ℝ) →
      ∀ i : Fin 3, VerticalSection (rightSquares i.succ) x := by
    intro x hx0 hx1 i
    fin_cases i
    · exact neighbor_cover_sound rightLo rightHi continuousScout898Domain3_3Ids
        RightNeighbors.neighbors0 RightNeighbors.neighbors0_covered
        RightNeighbors.neighbors0_checked (q 4) (ha 4) hn3 x hx0 hx1
    · exact neighbor_cover_sound rightLo rightHi continuousScout898Domain6_5Ids
        RightNeighbors.neighbors1 RightNeighbors.neighbors1_covered
        RightNeighbors.neighbors1_checked (q 5) (ha 5) hn4 x hx0 hx1
    · exact neighbor_cover_sound rightLo rightHi continuousScout898Domain9_8Ids
        RightNeighbors.neighbors2 RightNeighbors.neighbors2_covered
        RightNeighbors.neighbors2_checked (q 6) (ha 6) hn5 x hx0 hx1
  apply direct_cover continuousScout898Domain5_0Ids continuousScout898Domain5_11Ids
    plans plans_covered plans_checked (q 0) hs
  intro source _ source_holds
  exact ⟨left_window leftSquares source (fun i => ha _) (fun i => hb _)
      leftApart cap left right source_holds leftSections,
    right_window rightSquares source (fun i => ha _) (fun i => hb _)
      rightApart cap left right source_holds rightSections⟩

#print axioms chord_fused
end N12Compact.C898Chord.Fused
