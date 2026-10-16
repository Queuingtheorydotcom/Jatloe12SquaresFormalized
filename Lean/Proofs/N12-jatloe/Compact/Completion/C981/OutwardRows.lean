import Compact.Completion.C981.WallAdvance
import Compact.Completion.C981.OutwardAnchor
import Completion.Cases.C981.VectorData
import S12.TransformFacts

/-! Whole original representatives 24, 26 and 39. The advanced segment
belongs to the actual bottom-wall owner 9; its foreign singleton seed
belongs to owner 0. Every entrance fact is checked in the original row. -/
namespace N12Compact.C981CompletionOutwardRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 0 => [(187/100,19/25)]
  | 2 => [(3,1)]
  | 5 => [(47/20,33/20),(2,87/50),(3,8/5)]
  | 9 => [(2,457/500),(12/5,1),(113/50,1)]
  | 10 => [(1543/500,2)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 5 => [(113/50,2)]
  | 9 => [(87/50,1)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i,
    P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i,
    P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The outward-anchor contradiction uses only the stated actual square
points, exclusions, container bounds and disjoint interiors. It can therefore
be transported together with all owners by a container symmetry. -/
theorem geometry (q : Fin 12 → OpenSquare)
    (side : ∀ i, 1 < (q i).side)
    (box : ∀ i, InsideContainer (q i))
    (inside : ∀ i, ∀ P ∈ insidePoints i, (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (outside : ∀ i, ∀ P ∈ outsidePoints i, ¬ (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (apart : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) :
    False := by
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact apart i j different x y ⟨own,point⟩
  let g : Transform := ⟨true,false,false⟩
  let W := g.pull (q 9)
  have wallOwn (P : ℚ × ℚ) (point : (q 9).Inside P.2 P.1) :
      W.Inside P.1 P.2 := by
    apply (rat_inside_transform g (q 9) P).mpr
    simpa [g,Transform.applyRat] using point
  have wallOutside (P : ℚ × ℚ) (absent : ¬ (q 9).Inside P.2 P.1) :
      ¬ W.Inside P.1 P.2 := by
    intro point
    apply absent
    have original := (rat_inside_transform g (q 9) P).mp point
    simpa [g,Transform.applyRat] using original
  have wMarker : W.Inside (457/500) 2 := by
    have h := wallOwn ((457/500,2) : ℚ × ℚ)
      (by simpa using inside 9 (2,457/500) (by norm_num [insidePoints]))
    norm_num at h
    exact h
  have wUpper : W.Inside 1 (12/5) := by
    have h := wallOwn ((1,12/5) : ℚ × ℚ)
      (by simpa using inside 9 (12/5,1) (by norm_num [insidePoints]))
    norm_num at h
    exact h
  have wLow : ¬ W.Inside 1 (87/50) := by
    have h := wallOutside ((1,87/50) : ℚ × ℚ)
      (by simpa using outside 9 (87/50,1) (by norm_num [outsidePoints]))
    norm_num at h
    exact h
  have wSeed : ¬ W.Inside (19/25) (187/100) := by
    have h := wallOutside ((19/25,187/100) : ℚ × ℚ)
      (foreign 9 0 (by decide) _ _
        (by simpa using inside 0 (187/100,19/25) (by norm_num [insidePoints])))
    norm_num at h
    exact h
  have wCentral : ¬ W.Inside (33/20) (47/20) := by
    have h := wallOutside ((33/20,47/20) : ℚ × ℚ)
      (foreign 9 5 (by decide) _ _
        (by simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints])))
    norm_num at h
    exact h
  have reach := C981CompletionWallAdvance.point W
    (by simpa only [W,pull_same_side] using side 9)
    (container_transform g _ (box 9))
    wMarker wUpper wLow wSeed wCentral
  have far : (q 9).Inside (14/5) 1 := by
    have original := (inside_pull g (q 9) 1 (14/5)).mp reach
    simpa [g,Transform.apply] using original
  have near : (q 9).Inside (113/50) 1 := by
    simpa using inside 9 (113/50,1) (by norm_num [insidePoints])
  have segment (z : ℝ) (lo : 113/50 ≤ z) (hi : z ≤ 14/5) :
      (q 9).Inside z 1 := by
    let t := (z-113/50)/(14/5-113/50)
    have tn : 0 ≤ t := div_nonneg (by linarith only [lo]) (by norm_num)
    have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 14/5-113/50)).mpr
      (by linarith only [hi])
    have point := inside_segment (q 9) (113/50) 1 (14/5) 1 t near far tn tu
    convert point using 1 <;> dsimp [t] <;> ring
  apply C981CompletionOutwardAnchor.impossible (q 5) (side 5)
  · simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints])
  · simpa using inside 5 (2,87/50) (by norm_num [insidePoints])
  · simpa using inside 5 (3,8/5) (by norm_num [insidePoints])
  · apply foreign 5 2 (by decide)
    simpa using inside 2 (3,1) (by norm_num [insidePoints])
  · apply foreign 5 10 (by decide)
    simpa using inside 10 (1543/500,2) (by norm_num [insidePoints])
  · simpa using outside 5 (113/50,2) (by norm_num [outsidePoints])
  · intro z lo hi
    exact foreign 5 9 (by decide) z 1 (segment z lo hi)

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
  exact geometry (owners p) (owners_side_gt p) (owners_contained p) inside outside
    (fun i j different => owners_disjoint p hf i j different)

def coveredIds : List Nat := [24,26,39]

theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by
  decide +kernel

theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i member)

#print axioms covered_excluded
end N12Compact.C981CompletionOutwardRows
