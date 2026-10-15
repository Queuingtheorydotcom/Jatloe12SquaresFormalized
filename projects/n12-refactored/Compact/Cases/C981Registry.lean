import Completion.Cases.C981.VectorData
import Compact.Bridge.C981RotatedEndpointRows
import Compact.Bridge.C981DiagonalOuter
import Compact.Bridge.C981WallElbows
import Compact.Bridge.C981DoubleWallElbows
import Compact.Bridge.C981FullAuxNegative
import Compact.Bridge.C981DiagonalCornerElbows
import Compact.Bridge.C981DiagonalOuterElbows
import Compact.Bridge.C981TwoTipRows
import Compact.Bridge.C981Row27
import Compact.Bridge.C981InwardWallRows
import Compact.Completion.C981.OutwardRows
import Compact.Completion.C981.ShortRows.CoreRows
import Compact.Completion.C981.ShortWallRows
import Compact.Completion.C981.ShortWall71
import Compact.Cases.C981V116
import Compact.Assembly.C981Progress

/-! Honest compact completion boundary for the entire original C981 case.
The literal original vector contracts are imported, and the shared endpoint
proofs, the diagonal endpoint proof, the all-angle opposite-elbow proof,
the double-auxiliary wall proof, the shared representatives-3/4 support cycle,
the shared diagonal-corner proof for representatives 5, 6 and 42,
the outer-elbow proof for 35 and 60, the eleven two-tip proofs, row 27,
the inward-wall proofs for 36 and 106, the outward proofs for24,26,39,
the short core proof for101, the short wall cycle for59,105,108,
the short wall proof for 71, V116, and the twenty simplified completion
contracts are consumed. No representative-vector obligations remain.
The full actual domain/symmetry cover is imported by C981Compact separately,
and acceptance of that original enumeration remains a separate check. -/
namespace N12Compact.C981Compact
open S12 S12Completion S12Completion.C981
set_option Elab.async false

def baseCoveredIds : List Nat :=
  (((C981RotatedEndpointRows.coveredIds ++ C981DiagonalOuter.coveredIds) ++
    (C981WallElbows.coveredIds ++ C981DoubleWallElbows.coveredIds)) ++
    C981TwoTipRows.coveredIds) ++ C981InwardWallRows.coveredIds

def previousCoveredIds : List Nat :=
  (baseCoveredIds ++ C981CompletionOutwardRows.coveredIds) ++
    C981CompletionShortWallRows.coveredIds

def coveredIds : List Nat := previousCoveredIds ++ C981Progress.completionIds

def unfinished : List Nat :=
  (List.range 117).filter (fun i =>
    decide (i ∉ coveredIds ∧ i ≠ 27 ∧ i ≠ 116 ∧ i ≠ 4 ∧ i ≠ 6 ∧ i ≠ 5 ∧ i ≠ 42 ∧ i ≠ 3 ∧
      i ≠ 35 ∧ i ≠ 60 ∧ i ≠ 101 ∧ i ≠ 71))

def Pending : Prop :=
  ∀ i : Fin 117, i.val ∈ unfinished → ExcludesVector (representativeVectors[i.val]!)

/-- The sixteen whole wall/elbow endings overlap the earlier source in
exactly 7, 110 and 116. These thirteen entries are newly discharged. -/
theorem wall_new_ids : C981WallElbows.coveredIds.filter (fun i =>
    decide (i ∉ C981RotatedEndpointRows.coveredIds ∧
      i ∉ C981DiagonalOuter.coveredIds ∧ i ≠ 116)) =
    [0,8,19,22,44,50,52,53,66,111,113,114,115] := by decide +kernel

/-- All six newly coupled double-wall endings were previously unfinished. -/
theorem double_wall_new_ids : C981DoubleWallElbows.coveredIds.filter (fun i =>
    decide (i ∉ C981RotatedEndpointRows.coveredIds ∧
      i ∉ C981DiagonalOuter.coveredIds ∧ i ∉ C981WallElbows.coveredIds ∧ i ≠ 116)) =
    [1,20,21,23,51,112] := by decide +kernel

/-- The eleven all-orientation two-tip exclusions supply whole vectors. -/
theorem two_tip_new_ids : C981TwoTipRows.coveredIds.filter (fun i =>
    decide (i ∉ C981RotatedEndpointRows.coveredIds ∧
      i ∉ C981DiagonalOuter.coveredIds ∧ i ∉ C981WallElbows.coveredIds ∧
      i ∉ C981DoubleWallElbows.coveredIds ∧ i ≠ 116 ∧ i ≠ 4 ∧ i ≠ 6 ∧
      i ≠ 5 ∧ i ≠ 42 ∧ i ≠ 3 ∧ i ≠ 35 ∧ i ≠ 60)) =
    [25,31,40,70,32,33,38,57,99,94,95] := by decide +kernel

theorem unfinished_count : unfinished.length = 0 := by decide +kernel

/-- Every original representative has a supplied full-vector contract. -/
theorem unfinished_ids : unfinished = [] := by decide +kernel

/-- Preserve the existing conditional assembly API while supplying its now
empty representative boundary by an ordinary proof. -/
theorem pending_closed : Pending := by
  intro i member
  simp only [unfinished_ids,List.not_mem_nil] at member

theorem all_representatives (pending : Pending) (i : Fin 117) :
    ExcludesVector (representativeVectors[i.val]!) := by
  by_cases known : i.val ∈ coveredIds
  · rcases List.mem_append.mp known with previous | completed
    · rcases List.mem_append.mp previous with previousRows | shortWall
      · rcases List.mem_append.mp previousRows with previousRows | outward
        · rcases List.mem_append.mp previousRows with previous | inwardWall
          · rcases List.mem_append.mp previous with earlier | twoTip
            · rcases List.mem_append.mp earlier with endpoints | walls
              · rcases List.mem_append.mp endpoints with endpoint | diagonal
                · exact C981RotatedEndpointRows.covered_excluded i.val endpoint
                · exact C981DiagonalOuter.covered_excluded i.val diagonal
              · rcases List.mem_append.mp walls with ordinary | double
                · exact C981WallElbows.covered_excluded i.val ordinary
                · exact C981DoubleWallElbows.covered_excluded i.val double
            · exact C981TwoTipRows.covered_excluded i.val twoTip
          · exact C981InwardWallRows.covered_excluded i.val inwardWall
        · exact C981CompletionOutwardRows.covered_excluded i.val outward
      · exact C981CompletionShortWallRows.covered_excluded i.val shortWall
    · exact C981Progress.completion_excluded i.val completed
  by_cases row27 : i.val = 27
  · simpa only [row27] using C981Row27.representative27_excluded
  by_cases last : i.val = 116
  · simpa only [last] using C981V116.representative116_excluded
  by_cases fullAux : i.val = 4
  · simpa only [fullAux] using C981FullAuxNegative.representative4_excluded
  by_cases diagonalWall : i.val = 6
  · simpa only [diagonalWall] using C981DiagonalCornerElbows.representative6_excluded
  by_cases diagonalCorner : i.val = 5
  · simpa only [diagonalCorner] using C981DiagonalCornerElbows.representative5_excluded
  by_cases strongerDiagonal : i.val = 42
  · simpa only [strongerDiagonal] using C981DiagonalCornerElbows.representative42_excluded
  by_cases shortTop : i.val = 3
  · simpa only [shortTop] using C981FullAuxNegative.representative3_excluded
  by_cases outer : i.val = 35
  · simpa only [outer] using C981DiagonalOuterElbows.representative35_excluded
  by_cases strongerOuter : i.val = 60
  · simpa only [strongerOuter] using C981DiagonalOuterElbows.representative60_excluded
  by_cases shortCore : i.val = 101
  · simpa only [shortCore] using C981CompletionShortRows.representative101_excluded
  by_cases row71 : i.val = 71
  · simpa only [row71] using C981CompletionShortWall71.representative71_excluded
  · exact pending i (List.mem_filter.mpr
      ⟨List.mem_range.mpr i.isLt,
        decide_eq_true
          ⟨known,row27,last,fullAux,diagonalWall,diagonalCorner,strongerDiagonal,shortTop,outer,strongerOuter,shortCore,row71⟩⟩)


/-- All original representatives, with no remaining proof argument. -/
theorem all_representatives_complete (i : Fin 117) :
    ExcludesVector (representativeVectors[i.val]!) :=
  all_representatives pending_closed i

#print axioms all_representatives_complete
#print axioms all_representatives
end N12Compact.C981Compact
