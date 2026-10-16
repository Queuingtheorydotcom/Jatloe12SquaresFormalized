import Compact.Completion.C981.ShortCentralPair
import Compact.Completion.C981.Crosspoint
import Compact.Completion.C981.WallAdvance
import Compact.Geometry.CentralWallCenter
import Completion.Cases.C981.VectorData

/-! Original rows 93 and 98 share a northeast central owner and two
outward neighbors. The actual bottom/left walls supply the long segments;
the actual right/top walls supply the center and short crosspoints.
The central canonical sign chooses one of the two outward neighbors.
Source candidate: acceptance requires serial replay. -/
namespace N12Compact.C981CompletionShortCentralRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 0 => [(187/100,19/25)]
  | 1 => [(19/25,187/100)]
  | 2 => [(3,1)]
  | 4 => [(1,3)]
  | 5 => [(47/20,33/20),(3,8/5)]
  | 6 => [(47/20,47/20),(2,113/50),(113/50,2)]
  | 7 => [(33/20,47/20),(8/5,3)]
  | 8 => [(457/500,2),(1,12/5),(1,113/50)]
  | 9 => [(2,457/500),(12/5,1),(113/50,1)]
  | 10 => [(1543/500,2),(3,12/5)]
  | 11 => [(2,1543/500),(12/5,3)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 8 => [(1,87/50)]
  | 9 => [(87/50,1)]
  | 10 => [(3,87/50)]
  | 11 => [(87/50,3)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem wall_segment (W : OpenSquare) (side : 1 < W.side)
    (box : InsideContainer W) (marker : W.Inside (457/500) 2)
    (high : W.Inside 1 (12/5)) (low : W.Inside 1 (113/50))
    (missingLow : ¬ W.Inside 1 (87/50))
    (missingSeed : ¬ W.Inside (19/25) (187/100))
    (missingCentral : ¬ W.Inside (33/20) (47/20)) :
    ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → W.Inside 1 z := by
  have far := C981CompletionWallAdvance.point W side box marker high
    missingLow missingSeed missingCentral
  intro z lo hi
  let t := (z-113/50)/(14/5-113/50)
  have tn : 0 ≤ t := div_nonneg (by linarith only [lo]) (by norm_num)
  have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 14/5-113/50)).mpr
    (by linarith only [hi])
  have point := inside_segment W 1 (113/50) 1 (14/5) t low far tn tu
  convert point using 1 <;> dsimp [t] <;> ring

private noncomputable def swapFrame (q : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (turnFrame (pullSwap q)))

@[simp] private theorem swapFrame_c (q : OpenSquare) : (swapFrame q).c=q.c := by
  simp [swapFrame,turnFrame,pullSwap]
@[simp] private theorem swapFrame_s (q : OpenSquare) : (swapFrame q).s= -q.s := by
  simp [swapFrame,turnFrame,pullSwap]
@[simp] private theorem swapFrame_side (q : OpenSquare) : (swapFrame q).side=q.side := rfl
private theorem inside_swapFrame (q : OpenSquare) (x y : ℝ) :
    (swapFrame q).Inside x y ↔ q.Inside y x := by
  simp [swapFrame,inside_pullSwap]

theorem geometry (q : Fin 12 → OpenSquare)
    (side : ∀ i, 1 < (q i).side)
    (same : ∀ i j, (q i).side=(q j).side)
    (box : ∀ i, InsideContainer (q i))
    (inside : ∀ i, ∀ P ∈ insidePoints i, (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (outside : ∀ i, ∀ P ∈ outsidePoints i, ¬ (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (apart : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) :
    False := by
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact apart i j different x y ⟨own,point⟩
  have cMarker : (q 6).Inside (47/20) (47/20) := by
    simpa using inside 6 (47/20,47/20) (by norm_num [insidePoints])
  have cNorth : (q 6).Inside 2 (113/50) := by
    simpa using inside 6 (2,113/50) (by norm_num [insidePoints])
  have cEast : (q 6).Inside (113/50) 2 := by
    simpa using inside 6 (113/50,2) (by norm_num [insidePoints])
  have seMarker : (q 5).Inside (47/20) (33/20) := by
    simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints])
  have nwMarker : (q 7).Inside (33/20) (47/20) := by
    simpa using inside 7 (33/20,47/20) (by norm_num [insidePoints])
  have rMarker : (q 10).Inside (1543/500) 2 := by
    simpa using inside 10 (1543/500,2) (by norm_num [insidePoints])
  have rHigh : (q 10).Inside 3 (12/5) := by
    simpa using inside 10 (3,12/5) (by norm_num [insidePoints])
  have rMissing : ¬ (q 10).Inside 3 (87/50) := by
    simpa using outside 10 (3,87/50) (by norm_num [outsidePoints])
  have tMarker : (q 11).Inside 2 (1543/500) := by
    simpa using inside 11 (2,1543/500) (by norm_num [insidePoints])
  have tHigh : (q 11).Inside (12/5) 3 := by
    simpa using inside 11 (12/5,3) (by norm_num [insidePoints])
  have tMissing : ¬ (q 11).Inside (87/50) 3 := by
    simpa using outside 11 (87/50,3) (by norm_num [outsidePoints])
  have center : (q 6).Inside 2 2 :=
    CentralWallCenter.point (q 6) (q 10) (q 11) (side 6) (same 6 10) (same 6 11)
      (box 10) (box 11) cNorth cEast cMarker
      (foreign 6 5 (by decide) _ _ seMarker) (foreign 6 7 (by decide) _ _ nwMarker)
      rMarker rHigh rMissing tMarker tHigh tMissing
      (apart 6 10 (by decide)) (apart 6 11 (by decide))
  have rFar : (q 10).Inside 3 (5/2) :=
    CentralWallCenter.right_high (q 10) (side 10) (box 10) rMarker rHigh rMissing
      (foreign 10 6 (by decide) _ _ cEast)
  have tFar : (q 11).Inside (5/2) 3 := by
    have point := CentralWallCenter.right_high (pullSwap (q 11)) (side 11)
      (container_pullSwap _ (box 11))
      ((inside_pullSwap _ _ _).mpr tMarker) ((inside_pullSwap _ _ _).mpr tHigh)
      (fun h => tMissing ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 11 6 (by decide) _ _ cNorth ((inside_pullSwap _ _ _).mp h))
    exact (inside_pullSwap _ _ _).mp point
  have north : (q 6).Inside 2 (5/2) :=
    C981CompletionCrosspoint.point (q 6) (side 6) cNorth cEast cMarker
      (foreign 6 5 (by decide) _ _ seMarker) (foreign 6 7 (by decide) _ _ nwMarker)
      (foreign 6 10 (by decide) _ _ rHigh) (foreign 6 10 (by decide) _ _ rFar)
  have east : (q 6).Inside (5/2) 2 := by
    have point := C981CompletionCrosspoint.point (pullSwap (q 6)) (side 6)
      ((inside_pullSwap _ _ _).mpr cEast) ((inside_pullSwap _ _ _).mpr cNorth)
      ((inside_pullSwap _ _ _).mpr cMarker)
      (fun h => foreign 6 7 (by decide) _ _ nwMarker ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 6 5 (by decide) _ _ seMarker ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 6 11 (by decide) _ _ tHigh ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 6 11 (by decide) _ _ tFar ((inside_pullSwap _ _ _).mp h))
    exact (inside_pullSwap _ _ _).mp point
  have leftSegment : ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → (q 8).Inside 1 z := by
    apply wall_segment (q 8) (side 8) (box 8)
    · simpa using inside 8 (457/500,2) (by norm_num [insidePoints])
    · simpa using inside 8 (1,12/5) (by norm_num [insidePoints])
    · simpa using inside 8 (1,113/50) (by norm_num [insidePoints])
    · simpa using outside 8 (1,87/50) (by norm_num [outsidePoints])
    · exact foreign 8 1 (by decide) _ _
        (by simpa using inside 1 (19/25,187/100) (by norm_num [insidePoints]))
    · exact foreign 8 7 (by decide) _ _ nwMarker
  have bottomSegment : ∀ z : ℝ, 113/50 ≤ z → z ≤ 273/100 → (q 9).Inside z 1 := by
    have segment := wall_segment (pullSwap (q 9)) (side 9) (container_pullSwap _ (box 9))
      ((inside_pullSwap _ _ _).mpr
        (by simpa using inside 9 (2,457/500) (by norm_num [insidePoints])))
      ((inside_pullSwap _ _ _).mpr
        (by simpa using inside 9 (12/5,1) (by norm_num [insidePoints])))
      ((inside_pullSwap _ _ _).mpr
        (by simpa using inside 9 (113/50,1) (by norm_num [insidePoints])))
      (fun h => (show ¬ (q 9).Inside (87/50) 1 from by
          simpa using outside 9 (87/50,1) (by norm_num [outsidePoints]))
        ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 9 0 (by decide) _ _
        (by simpa using inside 0 (187/100,19/25) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 9 5 (by decide) _ _ seMarker ((inside_pullSwap _ _ _).mp h))
    intro z lo hi
    exact (inside_pullSwap _ _ _).mp (segment z lo hi)
  obtain ⟨A,ac,canon,aside,ai,_⟩ := ClosedFrames.canonical_frame (q 6)
  have aSide : 1 < A.side := by simpa only [aside] using side 6
  by_cases negative : A.s ≤ 0
  · apply C981CompletionShortCentralPair.impossible A (q 5) ac negative canon aSide
      (aside.trans (same 6 5)) ((ai _ _).mpr center) ((ai _ _).mpr north)
      ((ai _ _).mpr cMarker)
      (fun h => foreign 6 7 (by decide) _ _ nwMarker ((ai _ _).mp h)) seMarker
    · simpa using inside 5 (3,8/5) (by norm_num [insidePoints])
    · exact foreign 5 2 (by decide) _ _
        (by simpa using inside 2 (3,1) (by norm_num [insidePoints]))
    · exact foreign 5 10 (by decide) _ _ rMarker
    · exact foreign 5 6 (by decide) _ _ cEast
    · exact foreign 5 9 (by decide) _ _
        (by simpa using inside 9 (12/5,1) (by norm_num [insidePoints]))
    · intro z lo hi
      exact foreign 5 9 (by decide) _ _ (bottomSegment z lo hi)
    · intro x y h
      exact apart 6 5 (by decide) x y ⟨(ai _ _).mp h.1,h.2⟩
  · apply C981CompletionShortCentralPair.impossible (swapFrame A) (pullSwap (q 7))
      (by simpa only [swapFrame_c] using ac)
      (by simp only [swapFrame_s]; linarith only [negative])
      (by simpa only [swapFrame_c,swapFrame_s,abs_neg] using canon)
      (by simpa only [swapFrame_side] using aSide)
      (by change A.side=(q 7).side; exact aside.trans (same 6 7))
    · exact (inside_swapFrame _ _ _).mpr ((ai _ _).mpr center)
    · exact (inside_swapFrame _ _ _).mpr ((ai _ _).mpr east)
    · exact (inside_swapFrame _ _ _).mpr ((ai _ _).mpr cMarker)
    · intro h
      exact foreign 6 5 (by decide) _ _ seMarker
        ((ai _ _).mp ((inside_swapFrame _ _ _).mp h))
    · exact (inside_pullSwap _ _ _).mpr nwMarker
    · exact (inside_pullSwap _ _ _).mpr
        (by simpa using inside 7 (8/5,3) (by norm_num [insidePoints]))
    · intro h
      exact foreign 7 4 (by decide) _ _
        (by simpa using inside 4 (1,3) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp h)
    · intro h
      exact foreign 7 11 (by decide) _ _ tMarker ((inside_pullSwap _ _ _).mp h)
    · intro h
      exact foreign 7 6 (by decide) _ _ cNorth ((inside_pullSwap _ _ _).mp h)
    · intro h
      exact foreign 7 8 (by decide) _ _
        (by simpa using inside 8 (1,12/5) (by norm_num [insidePoints]))
        ((inside_pullSwap _ _ _).mp h)
    · intro z lo hi h
      exact foreign 7 8 (by decide) _ _ (leftSegment z lo hi) ((inside_pullSwap _ _ _).mp h)
    · intro x y h
      exact apart 6 7 (by decide) y x
        ⟨(ai _ _).mp ((inside_swapFrame _ _ _).mp h.1),(inside_pullSwap _ _ _).mp h.2⟩

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  have aux (i : Fin 12) : AuxExact (owners p i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ insidePoints i) :
      (owners p i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (owners p i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ (checked.2 i P member)
  exact geometry (owners p) (owners_side_gt p)
    (fun i j => (p.congruent _).trans (p.congruent _).symm)
    (owners_contained p) inside outside (fun i j different => owners_disjoint p hf i j different)

def coveredIds : List Nat := [93,98]
theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by decide +kernel
theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i member)

#print axioms covered_excluded
end N12Compact.C981CompletionShortCentralRows
