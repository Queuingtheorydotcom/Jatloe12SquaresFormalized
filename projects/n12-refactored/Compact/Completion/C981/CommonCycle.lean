import Compact.Completion.C981.UpperPoint
import Compact.Completion.C981.CentralPositivePoint
import Compact.Completion.C981.NegativePair
import Compact.Completion.C981.SteepPositivePair
import S12.SymmetryBase

/-! Shared all-orientation geometric ending for the eight common C981
rows. Its center, crosspoints, complete wall segment and all foreign
absences are entrance obligations, to be derived from the actual owners. -/
namespace N12Compact.C981CompletionCommonCycle

open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private noncomputable def rotate (q : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (turnFrame (pullSwap (pullY q))))

@[simp] private theorem rotate_c (q : OpenSquare) : (rotate q).c=q.c := by
  simp [rotate,turnFrame,pullSwap,pullY]
@[simp] private theorem rotate_s (q : OpenSquare) : (rotate q).s=q.s := by
  simp [rotate,turnFrame,pullSwap,pullY]
@[simp] private theorem rotate_side (q : OpenSquare) : (rotate q).side=q.side := rfl

private theorem inside_rotate (q : OpenSquare) (x y : ℝ) :
    (rotate q).Inside x y ↔ q.Inside y (4-x) := by
  simp [rotate,inside_pullSwap,inside_pullY]

/-- Both central squares are actual physical owners. Every continuous
canonical sign, including zero and diagonal frames, is covered. -/
theorem impossible (C B : OpenSquare) (side : 1 < C.side) (same : C.side=B.side)
    (center : C.Inside 2 2) (west : C.Inside (3/2) 2) (north : C.Inside 2 (5/2))
    (cMarker : C.Inside (33/20) (47/20))
    (missingSW : ¬ C.Inside (33/20) (33/20))
    (wallSegment : ∀ y : ℝ, 113/50 ≤ y → y ≤ 14/5 → ¬ C.Inside 1 y)
    (bMarker : B.Inside (47/20) (47/20))
    (bTopLow : B.Inside (113/50) 3) (bTopHigh : B.Inside (12/5) 3)
    (bMissingLowerLeft : ¬ B.Inside 2 (12/5))
    (bMissingUpperLeft : ¬ B.Inside 2 3)
    (bMissingLowerRight : ¬ B.Inside 3 (12/5))
    (bMissingUpperRight : ¬ B.Inside 3 3)
    (bMissingRight : ¬ B.Inside 3 (64/25))
    (bMissingRightMid : ¬ B.Inside 3 (5/2))
    (bMissingTopMarker : ¬ B.Inside 2 (1543/500))
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  obtain ⟨A,ac,canon,aside,ai,_⟩ := ClosedFrames.canonical_frame C
  obtain ⟨D,dc,dcanon,dside,di,_⟩ := ClosedFrames.canonical_frame B
  have aSide : 1 < A.side := by simpa only [aside] using side
  have dSide : 1 < D.side := by simpa only [dside,←same] using side
  have congruent : A.side=D.side := aside.trans (same.trans dside.symm)
  have aCenter := (ai _ _).mpr center
  have aWest := (ai _ _).mpr west
  have aNorth := (ai _ _).mpr north
  have aMarker := (ai _ _).mpr cMarker
  have aMissing : ¬ A.Inside (33/20) (33/20) := fun h => missingSW ((ai _ _).mp h)
  have aWall : ∀ y : ℝ, 113/50 ≤ y → y ≤ 14/5 → ¬ A.Inside 1 y := by
    intro y lo hi point
    exact wallSegment y lo hi ((ai _ _).mp point)
  have dMarker := (di _ _).mpr bMarker
  have dLow := (di _ _).mpr bTopLow
  have dHigh := (di _ _).mpr bTopHigh
  have dLL : ¬ D.Inside 2 (12/5) := fun h => bMissingLowerLeft ((di _ _).mp h)
  have dUL : ¬ D.Inside 2 3 := fun h => bMissingUpperLeft ((di _ _).mp h)
  have dLR : ¬ D.Inside 3 (12/5) := fun h => bMissingLowerRight ((di _ _).mp h)
  have dUR : ¬ D.Inside 3 3 := fun h => bMissingUpperRight ((di _ _).mp h)
  have dR : ¬ D.Inside 3 (64/25) := fun h => bMissingRight ((di _ _).mp h)
  have framesApart : ∀ x y, ¬(A.Inside x y ∧ D.Inside x y) := by
    intro x y h
    exact apart x y ⟨(ai _ _).mp h.1,(di _ _).mp h.2⟩
  have shared := C981CompletionUpperPoint.point D dSide dMarker dLow dLL dUL dLR dUR dR
  by_cases positive : 0 ≤ A.s
  · have missingNE : ¬ A.Inside (47/20) (47/20) := fun h => framesApart _ _ ⟨h,dMarker⟩
    exact framesApart 2 (131/50)
      ⟨C981CompletionCentralPositivePoint.point A aSide ac positive
        (by simpa only [abs_of_nonneg positive] using canon)
        aCenter aWest aNorth aMarker aMissing missingNE aWall,shared⟩
  · let r := -A.s
    let C' := rotate A
    let B' := rotate D
    have cs : C'.s=-r := by simp [C',r]
    have cn : Normal C'.c r := by
      simp only [C',rotate_c]
      exact ⟨by dsimp [r]; linarith only [positive],
        by dsimp [r]; linarith only [(abs_le.mp canon).1],
        by dsimp [r]; nlinarith only [A.unit_normal]⟩
    have congruent' : C'.side=B'.side := by simpa only [C',B',rotate_side] using congruent
    have side' : 1 < C'.side := by simpa only [C',rotate_side] using aSide
    have cCenter : C'.Inside 2 2 := by
      apply (inside_rotate A _ _).mpr
      norm_num
      exact aCenter
    have cWest : C'.Inside (3/2) 2 := by
      apply (inside_rotate A _ _).mpr
      norm_num
      exact aNorth
    have cBottom : C'.Inside 2 (3/2) := by
      apply (inside_rotate A _ _).mpr
      norm_num
      exact aWest
    have cSW : C'.Inside (33/20) (33/20) := by
      apply (inside_rotate A _ _).mpr
      norm_num
      exact aMarker
    have cSE : ¬ C'.Inside (47/20) (33/20) := by
      intro point
      apply aMissing
      have h := (inside_rotate A _ _).mp point
      norm_num at h
      exact h
    have bNW : B'.Inside (33/20) (47/20) := by
      apply (inside_rotate D _ _).mpr
      norm_num
      exact dMarker
    have bLow : B'.Inside 1 (113/50) := by
      apply (inside_rotate D _ _).mpr
      norm_num
      exact dLow
    have bHigh : B'.Inside 1 (12/5) := by
      apply (inside_rotate D _ _).mpr
      norm_num
      exact dHigh
    have bCorner : ¬ B'.Inside 1 3 := by
      intro point
      apply dUR
      have h := (inside_rotate D _ _).mp point
      norm_num at h
      exact h
    have rotatedApart : ∀ x y, ¬(C'.Inside x y ∧ B'.Inside x y) := by
      intro x y h
      exact framesApart y (4-x)
        ⟨(inside_rotate A _ _).mp h.1,(inside_rotate D _ _).mp h.2⟩
    by_cases bPositive : 0 ≤ D.s
    · have bn : Normal B'.c B'.s := by
        simp only [B',rotate_c,rotate_s]
        exact ⟨bPositive,by simpa only [abs_of_nonneg bPositive] using dcanon,D.unit_normal⟩
      have steep := (C981CompletionUpperPoint.positive D dSide dc bPositive
        (by simpa only [abs_of_nonneg bPositive] using dcanon)
        dMarker dLow dLL dUL dLR dUR dR).1
      have bTop : ¬ B'.Inside (3/2) 3 := by
        intro point
        apply bMissingRightMid
        have h := (inside_rotate D _ _).mp point
        norm_num at h
        exact (di _ _).mp h
      apply C981CompletionSteepPositivePair.impossible C' B' r cs cn bn side' congruent'
        (by simpa only [B',rotate_c,rotate_s] using steep.le)
        cCenter cWest cBottom cSW cSE bNW bLow bHigh bTop bCorner rotatedApart
    · let t := -D.s
      have bs : B'.s=-t := by simp [B',t]
      have bn : Normal B'.c t := by
        simp only [B',rotate_c]
        exact ⟨by dsimp [t]; linarith only [bPositive],
          by dsimp [t]; linarith only [(abs_le.mp dcanon).1],
          by dsimp [t]; nlinarith only [D.unit_normal]⟩
      have bTop : ¬ B'.Inside (8/5) 3 := by
        intro point
        apply dLR
        have h := (inside_rotate D _ _).mp point
        norm_num at h
        exact h
      have bWall : ¬ B'.Inside (457/500) 2 := by
        intro point
        apply bMissingTopMarker
        have h := (inside_rotate D _ _).mp point
        norm_num at h
        exact (di _ _).mp h
      exact C981CompletionNegativePair.impossible C' B' r t cs cn bs bn side' congruent'
        cCenter cBottom cSW cSE bNW bHigh bTop bCorner bWall rotatedApart

#print axioms impossible
end N12Compact.C981CompletionCommonCycle
