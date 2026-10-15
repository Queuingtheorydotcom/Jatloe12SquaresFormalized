import Compact.Completion.C981.CommonCycle
import Compact.Completion.C981.LastNegativePair
import Compact.Completion.C981.LastPositivePair
import Compact.Completion.C981.OppositeAngle
import Compact.Completion.C981.LastRightWall

/-! Complete continuous ending of the last two original C981 cycles.
Every named square is a single actual owner throughout the rigid charts. -/
namespace N12Compact.C981CompletionLastCycle

open S12 S12Pilot C977CornerCubic
set_option Elab.async false

noncomputable def rotate (q : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (turnFrame (pullSwap (pullY q))))
@[simp] theorem rotate_c (q : OpenSquare) : (rotate q).c=q.c := by
  simp [rotate,turnFrame,pullSwap,pullY]
@[simp] theorem rotate_s (q : OpenSquare) : (rotate q).s=q.s := by
  simp [rotate,turnFrame,pullSwap,pullY]
@[simp] theorem rotate_side (q : OpenSquare) : (rotate q).side=q.side := rfl
theorem inside_rotate (q : OpenSquare) (x y : ℝ) :
    (rotate q).Inside x y ↔ q.Inside y (4-x) := by
  simp [rotate,inside_pullSwap,inside_pullY]

noncomputable def work (q : OpenSquare) : OpenSquare := (rotate q).translated 2 2
@[simp] theorem work_c (q : OpenSquare) : (work q).c=q.c := rotate_c q
@[simp] theorem work_s (q : OpenSquare) : (work q).s=q.s := rotate_s q
@[simp] theorem work_side (q : OpenSquare) : (work q).side=q.side := rfl
theorem inside_work (q : OpenSquare) (x y : ℝ) :
    (work q).Inside x y ↔ q.Inside (2+y) (2-x) := by
  rw [work,inside_translated_iff,inside_rotate]
  have identity : 4-(2+x)=2-x := by ring
  rw [identity]

theorem impossible (C B A R : OpenSquare)
    (side : 1 < C.side) (cap : C.side ≤ 1001/1000)
    (sameB : C.side=B.side) (sameA : C.side=A.side) (sameR : B.side=R.side)
    (rightWall : ∀ x y, R.Inside x y → x ≤ 4)
    (center : C.Inside 2 2) (west : C.Inside (3/2) 2) (north : C.Inside 2 (5/2))
    (cMarker : C.Inside (33/20) (47/20))
    (missingSW : ¬ C.Inside (33/20) (33/20))
    (leftSegment : ∀ y : ℝ, 113/50 ≤ y → y ≤ 14/5 → ¬ C.Inside 1 y)
    (topSegment : ∀ x : ℝ, 36/25 ≤ x → x ≤ 2 → ¬ C.Inside x 3)
    (bMarker : B.Inside (47/20) (47/20))
    (bLow : B.Inside (113/50) 3) (bHigh : B.Inside (12/5) 3)
    (bMissingCut : ¬ B.Inside 2 (12/5)) (bMissingOrigin : ¬ B.Inside 2 3)
    (bMissingRight : ¬ B.Inside 3 (12/5)) (bMissingCorner : ¬ B.Inside 3 3)
    (bMissingMarker : ¬ B.Inside 2 (1543/500))
    (aMarker : A.Inside (47/20) (33/20))
    (aInward : A.Inside 2 (87/50)) (aElbow : A.Inside (113/50) 2)
    (aMissingWall : ¬ A.Inside 3 (87/50))
    (aBottomSegment : ∀ x : ℝ, 113/50 ≤ x → x ≤ 14/5 → ¬ A.Inside x 1)
    (cMissingJ : ¬ C.Inside 1 (87/50))
    (rLower : R.Inside 3 (87/50)) (rUpper : R.Inside 3 (12/5))
    (rMissing : ¬ R.Inside 3 (8/5))
    (apartB : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y))
    (apartA : ∀ x y, ¬ (C.Inside x y ∧ A.Inside x y))
    (apartR : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) : False := by
  obtain ⟨F,fc,fcanon,fside,fi,_⟩ := ClosedFrames.canonical_frame C
  obtain ⟨G,gc,gcanon,gside,gi,_⟩ := ClosedFrames.canonical_frame B
  have fSide : 1 < F.side := by simpa only [fside] using side
  have gSide : 1 < G.side := by simpa only [gside,←sameB] using side
  have congruent : F.side=G.side := fside.trans (sameB.trans gside.symm)
  have fCenter := (fi _ _).mpr center
  have fWest := (fi _ _).mpr west
  have fNorth := (fi _ _).mpr north
  have fMarker := (fi _ _).mpr cMarker
  have fMissing : ¬ F.Inside (33/20) (33/20) := fun h => missingSW ((fi _ _).mp h)
  have fWall : ∀ y : ℝ, 113/50 ≤ y → y ≤ 14/5 → ¬ F.Inside 1 y := by
    intro y lo hi h
    exact leftSegment y lo hi ((fi _ _).mp h)
  have gMarker := (gi _ _).mpr bMarker
  have gLow := (gi _ _).mpr bLow
  have gHigh := (gi _ _).mpr bHigh
  have gCut : ¬ G.Inside 2 (12/5) := fun h => bMissingCut ((gi _ _).mp h)
  have gOrigin : ¬ G.Inside 2 3 := fun h => bMissingOrigin ((gi _ _).mp h)
  have gRight : ¬ G.Inside 3 (12/5) := fun h => bMissingRight ((gi _ _).mp h)
  have gCorner : ¬ G.Inside 3 3 := fun h => bMissingCorner ((gi _ _).mp h)
  have frameApart : ∀ x y, ¬ (F.Inside x y ∧ G.Inside x y) := by
    intro x y h
    exact apartB x y ⟨(fi _ _).mp h.1,(gi _ _).mp h.2⟩
  have positivePoint (sign : 0 ≤ F.s) : F.Inside 2 (131/50) :=
    C981CompletionCentralPositivePoint.point F fSide fc sign
      (by simpa only [abs_of_nonneg sign] using fcanon) fCenter fWest fNorth fMarker fMissing
      (fun h => frameApart _ _ ⟨h,gMarker⟩) fWall
  let C' := rotate F
  let B' := rotate G
  have same' : C'.side=B'.side := by simpa only [C',B',rotate_side] using congruent
  have side' : 1 < C'.side := by simpa only [C',rotate_side] using fSide
  have cCenter : C'.Inside 2 2 := by
    apply (inside_rotate F _ _).mpr
    norm_num
    exact fCenter
  have cWest : C'.Inside (3/2) 2 := by
    apply (inside_rotate F _ _).mpr
    norm_num
    exact fNorth
  have cBottom : C'.Inside 2 (3/2) := by
    apply (inside_rotate F _ _).mpr
    norm_num
    exact fWest
  have cSW : C'.Inside (33/20) (33/20) := by
    apply (inside_rotate F _ _).mpr
    norm_num
    exact fMarker
  have cSE : ¬ C'.Inside (47/20) (33/20) := by
    intro h
    apply fMissing
    have point := (inside_rotate F _ _).mp h
    norm_num at point
    exact point
  have bNW : B'.Inside (33/20) (47/20) := by
    apply (inside_rotate G _ _).mpr
    norm_num
    exact gMarker
  have bL : B'.Inside 1 (113/50) := by
    apply (inside_rotate G _ _).mpr
    norm_num
    exact gLow
  have bH : B'.Inside 1 (12/5) := by
    apply (inside_rotate G _ _).mpr
    norm_num
    exact gHigh
  have bK : ¬ B'.Inside 1 3 := by
    intro h
    apply gCorner
    have point := (inside_rotate G _ _).mp h
    norm_num at point
    exact point
  have bT : ¬ B'.Inside (8/5) 3 := by
    intro h
    apply gRight
    have point := (inside_rotate G _ _).mp h
    norm_num at point
    exact point
  have rotatedApart : ∀ x y, ¬ (C'.Inside x y ∧ B'.Inside x y) := by
    intro x y h
    exact frameApart y (4-x) ⟨(inside_rotate F _ _).mp h.1,(inside_rotate G _ _).mp h.2⟩
  by_cases gPositive : 0 ≤ G.s
  · have bn : Normal G.c G.s := ⟨gPositive,by simpa only [abs_of_nonneg gPositive] using gcanon,G.unit_normal⟩
    have bnRotated : Normal B'.c B'.s := by
      simpa only [B',rotate_c,rotate_s] using bn
    have bMissingLow : ¬ B'.Inside 1 2 := by
      intro h
      apply gOrigin
      have point := (inside_rotate G _ _).mp h
      norm_num at point
      exact point
    have bMissingInner : ¬ B'.Inside (8/5) 2 := by
      intro h
      apply gCut
      have point := (inside_rotate G _ _).mp h
      norm_num at point
      exact point
    have angle : 1/2 < G.s := by
      let W := work G
      let V := work R
      have wMarker : W.Inside (-(7/20)) (7/20) := by
        apply (inside_work G _ _).mpr
        norm_num
        exact gMarker
      have wLow : W.Inside (-1) (13/50) := by
        apply (inside_work G _ _).mpr
        norm_num
        exact gLow
      have wHigh : W.Inside (-1) (2/5) := by
        apply (inside_work G _ _).mpr
        norm_num
        exact gHigh
      have wMissing (x y : ℝ) (missing : ¬ G.Inside (2+y) (2-x)) : ¬ W.Inside x y :=
        fun h => missing ((inside_work G _ _).mp h)
      have vA : V.Inside (-(2/5)) 1 := by
        apply (inside_work R _ _).mpr
        norm_num
        exact rUpper
      have vD : V.Inside (13/50) 1 := by
        apply (inside_work R _ _).mpr
        norm_num
        exact rLower
      have vT : ¬ V.Inside (2/5) 1 := by
        intro h
        apply rMissing
        have point := (inside_work R _ _).mp h
        norm_num at point
        exact point
      have vWall : ∀ x y, V.Inside x y → y ≤ 2 := by
        intro x y h
        have bound := rightWall _ _ ((inside_work R _ _).mp h)
        linarith only [bound]
      have wrApart : ∀ x y, ¬ (W.Inside x y ∧ V.Inside x y) := by
        intro x y h
        exact apartR _ _ ⟨(gi _ _).mp ((inside_work G _ _).mp h.1),(inside_work R _ _).mp h.2⟩
      have wNormal : Normal W.c W.s := by
        simpa only [W,work_c,work_s] using bn
      have result := C981CompletionLastRightWall.angle W V wNormal gSide
        (by simpa only [W,V,work_side] using gside.trans sameR)
        wMarker wLow wHigh
        (wMissing (-1) 0 (by norm_num; exact gOrigin))
        (wMissing (-(2/5)) 0 (by norm_num; exact gCut))
        (wMissing (-1) 1 (by norm_num; exact gCorner))
        (wMissing (-(2/5)) 1 (by norm_num; exact gRight)) vWall vA vD vT wrApart
      simpa only [W,work_s] using result
    have angleRotated : 1/2 ≤ B'.s := by
      simpa only [B',rotate_s] using angle.le
    by_cases fPositive : 0 ≤ F.s
    · have cn : Normal F.c F.s := ⟨fPositive,by simpa only [abs_of_nonneg fPositive] using fcanon,F.unit_normal⟩
      let W := work F
      let V := work A
      obtain ⟨Q,qc,qs,qside,qi,_⟩ := ClosedFrames.positive_frame V
      have wInside (x y : ℝ) (point : F.Inside (2+y) (2-x)) : W.Inside x y :=
        (inside_work F _ _).mpr point
      have qNorth : Q.Inside 0 (13/50) := by
        apply (qi _ _).mpr
        apply (inside_work A _ _).mpr
        norm_num
        exact aElbow
      have qEast : Q.Inside (13/50) 0 := by
        apply (qi _ _).mpr
        apply (inside_work A _ _).mpr
        norm_num
        exact aInward
      have qMarker : Q.Inside (7/20) (7/20) := by
        apply (qi _ _).mpr
        apply (inside_work A _ _).mpr
        norm_num
        exact aMarker
      have wqApart : ∀ x y, ¬ (W.Inside x y ∧ Q.Inside x y) := by
        intro x y h
        exact apartA _ _ ⟨(fi _ _).mp ((inside_work F _ _).mp h.1),
          (inside_work A _ _).mp ((qi _ _).mp h.2)⟩
      have qO : ¬ Q.Inside 0 0 := by
        intro h
        apply wqApart 0 0
        exact ⟨wInside 0 0 (by norm_num; exact fCenter),h⟩
      have qF : ¬ Q.Inside (13/50) 1 := by
        intro h
        apply aMissingWall
        have point := (inside_work A _ _).mp ((qi _ _).mp h)
        norm_num at point
        exact point
      have qSegment : ∀ y : ℝ, 13/50 ≤ y → y ≤ 4/5 → ¬ Q.Inside 1 y := by
        intro y lo hi h
        apply aBottomSegment (2+y) (by linarith only [lo]) (by linarith only [hi])
        have point := (inside_work A _ _).mp ((qi _ _).mp h)
        norm_num at point
        exact point
      have wNW : ¬ W.Inside (-(7/20)) (7/20) := by
        intro h
        apply frameApart _ _
        have point := (inside_work F _ _).mp h
        norm_num at point
        exact ⟨point,gMarker⟩
      have wSE : ¬ W.Inside (7/20) (-(7/20)) := by
        intro h
        apply fMissing
        have point := (inside_work F _ _).mp h
        norm_num at point
        exact point
      have wBottom : ∀ x : ℝ, -(4/5) ≤ x → x ≤ -(13/50) → ¬ W.Inside x (-1) := by
        intro x lo hi h
        apply leftSegment (2-x) (by linarith only [hi]) (by linarith only [lo])
        have point := (inside_work F _ _).mp h
        norm_num at point
        exact (fi _ _).mp point
      have wLeft : ∀ y : ℝ, -(14/25) ≤ y → y ≤ 0 → ¬ W.Inside (-1) y := by
        intro y lo hi h
        apply topSegment (2+y) (by linarith only [lo]) (by linarith only [hi])
        have point := (inside_work F _ _).mp h
        norm_num at point
        exact (fi _ _).mp point
      have wcNormal : Normal W.c F.s := by
        simpa only [W,work_c] using cn
      have small := C981CompletionOppositeAngle.bound W Q F.s (by simp only [W,work_s]) wcNormal fSide
        (by simpa only [W,work_side,fside] using cap)
        (by simpa only [W,V,work_side] using fside.trans (sameA.trans qside.symm)) qc qs
        (wInside 0 0 (by norm_num; exact fCenter))
        (wInside (-(1/2)) 0 (by norm_num; exact fNorth))
        (wInside 0 (-(1/2)) (by norm_num; exact fWest))
        (wInside (-(7/20)) (-(7/20)) (by norm_num; exact fMarker))
        wNW wSE wBottom wLeft qNorth qEast qMarker qO qF qSegment wqApart
      have cFar : C'.Inside (69/50) 2 := by
        apply (inside_rotate F _ _).mpr
        norm_num
        exact positivePoint fPositive
      have cNW : ¬ C'.Inside (33/20) (47/20) := by
        intro h
        apply frameApart _ _
        have point := (inside_rotate F _ _).mp h
        norm_num at point
        exact ⟨point,gMarker⟩
      have diagonal : ∀ z : ℝ, 0 ≤ z → z ≤ 13/50 → ¬ C'.Inside (2+z) (113/50-z) := by
        intro z lo hi h
        let t := z/(13/50)
        have tn : 0 ≤ t := div_nonneg lo (by norm_num)
        have th : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 13/50)).mpr (by linarith only [hi])
        have owned := inside_segment A (113/50) 2 2 (87/50) t aElbow aInward tn th
        have point := (inside_rotate F _ _).mp h
        apply apartA (113/50-z) (2-z)
        refine ⟨(fi _ _).mp (by convert point using 1 <;> ring),?_⟩
        convert owned using 1 <;> dsimp [t] <;> ring
      have cnRotated : Normal C'.c F.s := by
        simpa only [C',rotate_c] using cn
      exact C981CompletionLastPositivePair.impossible C' B' F.s (by simp only [C',rotate_s]) cnRotated bnRotated side' same'
        (by simpa only [W,work_s] using small) angleRotated cCenter cFar cBottom cSW cNW cSE diagonal
        bNW bL bH bMissingLow bMissingInner bK bT rotatedApart
    · let r := -F.s
      have cs : C'.s=-r := by simp [C',r]
      have cn : Normal C'.c r := by
        simp only [C',rotate_c]
        exact ⟨by dsimp [r]; linarith only [fPositive],
          by dsimp [r]; linarith only [(abs_le.mp fcanon).1],
          by dsimp [r]; nlinarith only [F.unit_normal]⟩
      have missingD : ¬ C'.Inside (113/50) 2 := by
        intro h
        have point := (inside_rotate F _ _).mp h
        norm_num at point
        exact apartA _ _ ⟨(fi _ _).mp point,aInward⟩
      have missingJ : ¬ C'.Inside (113/50) 1 := by
        intro h
        apply cMissingJ
        have point := (inside_rotate F _ _).mp h
        norm_num at point
        exact (fi _ _).mp point
      exact C981CompletionLastNegativePair.impossible C' B' r cs cn bnRotated side' same' angleRotated
        cCenter cWest cBottom cSW cSE bNW bL bH bT bK missingD missingJ rotatedApart
  · have gNegative : G.s ≤ 0 := le_of_lt (lt_of_not_ge gPositive)
    by_cases fPositive : 0 ≤ F.s
    · have shared := C981CompletionUpperPoint.nonpositive G gSide gc gNegative
        (by linarith only [(abs_le.mp gcanon).1]) gMarker gLow gCut gOrigin gRight gCorner
      exact frameApart _ _ ⟨positivePoint fPositive,shared⟩
    · let r := -F.s
      let t := -G.s
      have cs : C'.s=-r := by simp [C',r]
      have bs : B'.s=-t := by simp [B',t]
      have cn : Normal C'.c r := by
        simp only [C',rotate_c]
        exact ⟨by dsimp [r]; linarith only [fPositive],
          by dsimp [r]; linarith only [(abs_le.mp fcanon).1],
          by dsimp [r]; nlinarith only [F.unit_normal]⟩
      have bn : Normal B'.c t := by
        simp only [B',rotate_c]
        exact ⟨by dsimp [t]; linarith only [gNegative],
          by dsimp [t]; linarith only [(abs_le.mp gcanon).1],
          by dsimp [t]; nlinarith only [G.unit_normal]⟩
      have bWall : ¬ B'.Inside (457/500) 2 := by
        intro h
        apply bMissingMarker
        have point := (inside_rotate G _ _).mp h
        norm_num at point
        exact (gi _ _).mp point
      exact C981CompletionNegativePair.impossible C' B' r t cs cn bs bn side' same'
        cCenter cBottom cSW cSE bNW bH bT bK bWall rotatedApart

#print axioms impossible
end N12Compact.C981CompletionLastCycle
