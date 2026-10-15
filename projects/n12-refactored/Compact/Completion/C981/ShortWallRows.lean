import Compact.Completion.C981.TopReach
import Compact.Completion.C981.ShortWallCycle
import Compact.Completion.C981.Charts
import Compact.Completion.C981.WallAdvance
import Completion.Cases.C981.VectorData

/-! Original whole-vector exclusions 59,105,108. Their actual top owner
reaches (2.73,3) by the origin/tip alternatives. Both central owners then
strictly contain (2.54,1.99). No ordinary-center conclusion is assumed. -/
namespace N12Compact.C981CompletionShortWallRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def insidePoints : Fin 12 → List (ℚ × ℚ)
  | 1 => [(19/25,187/100)]
  | 3 => [(3,3),(1543/500,3)]
  | 5 => [(47/20,33/20),(2,87/50),(113/50,2)]
  | 6 => [(47/20,47/20),(3,113/50),(3,12/5)]
  | 7 => [(33/20,47/20),(2,113/50),(87/50,3)]
  | 8 => [(457/500,2),(1,113/50),(1,12/5)]
  | 9 => [(12/5,1)]
  | 10 => [(1543/500,2)]
  | 11 => [(2,1543/500),(12/5,3),(113/50,3)]
  | _ => []

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 5 => [(33/20,33/20)]
  | 7 => [(8/5,3),(87/50,2)]
  | 8 => [(1,87/50)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem ending (q : Fin 12 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (same : ∀ i j, (q i).side=(q j).side)
    (inside : ∀ i, ∀ P ∈ insidePoints i, (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (missingSW : ¬ (q 5).Inside (33/20) (33/20))
    (topFar : (q 11).Inside (273/100) 3)
    (apart : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) :
    False := by
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact apart i j different x y ⟨own,point⟩
  have bMarker : (q 6).Inside (47/20) (47/20) := by
    simpa using inside 6 (47/20,47/20) (by norm_num [insidePoints])
  have topLow : (q 11).Inside (113/50) 3 := by
    simpa using inside 11 (113/50,3) (by norm_num [insidePoints])
  have topSegment (z : ℝ) (lo : 113/50 ≤ z) (hi : z ≤ 273/100) : (q 11).Inside z 3 := by
    let t := (z-113/50)/(273/100-113/50)
    have tn : 0 ≤ t := div_nonneg (by linarith only [lo]) (by norm_num)
    have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 273/100-113/50)).mpr
      (by linarith only [hi])
    have point := inside_segment (q 11) (113/50) 3 (273/100) 3 t topLow topFar tn tu
    convert point using 1 <;> dsimp [t] <;> ring
  apply C981CompletionShortWallCycle.impossible (q 5) (q 6) (side 5) (same 5 6)
    (by simpa using inside 5 (47/20,33/20) (by norm_num [insidePoints]))
    (by simpa using inside 5 (2,87/50) (by norm_num [insidePoints]))
    (by simpa using inside 5 (113/50,2) (by norm_num [insidePoints]))
    missingSW
    (foreign 5 6 (by decide) _ _ bMarker)
    (foreign 5 9 (by decide) _ _ (by simpa using inside 9 (12/5,1) (by norm_num [insidePoints])))
    bMarker
    (by simpa using inside 6 (3,113/50) (by norm_num [insidePoints]))
    (by simpa using inside 6 (3,12/5) (by norm_num [insidePoints]))
    (foreign 6 10 (by decide) _ _ (by simpa using inside 10 (1543/500,2) (by norm_num [insidePoints])))
    (foreign 6 11 (by decide) _ _ topLow) (foreign 6 11 (by decide) _ _ topFar)
    (foreign 6 3 (by decide) _ _ (by simpa using inside 3 (3,3) (by norm_num [insidePoints])))
    (foreign 6 3 (by decide) _ _ (by simpa using inside 3 (1543/500,3) (by norm_num [insidePoints])))
    (fun z lo hi => foreign 6 11 (by decide) _ _ (topSegment z lo hi))
    (apart 5 6 (by decide))

theorem geometry (q : Fin 12 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (same : ∀ i j, (q i).side=(q j).side)
    (box : ∀ i, InsideContainer (q i))
    (inside : ∀ i, ∀ P ∈ insidePoints i, (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (outside : ∀ i, ∀ P ∈ outsidePoints i, ¬ (q i).Inside (P.1 : ℝ) (P.2 : ℝ))
    (apart : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) :
    False := by
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact apart i j different x y ⟨own,point⟩
  have leftMarker : (q 8).Inside (457/500) 2 := by
    simpa using inside 8 (457/500,2) (by norm_num [insidePoints])
  have leftHigh : (q 8).Inside 1 (12/5) := by
    simpa using inside 8 (1,12/5) (by norm_num [insidePoints])
  have nMarker : (q 7).Inside (33/20) (47/20) := by
    simpa using inside 7 (33/20,47/20) (by norm_num [insidePoints])
  have bMarker : (q 6).Inside (47/20) (47/20) := by
    simpa using inside 6 (47/20,47/20) (by norm_num [insidePoints])
  have leftMissing : ¬ (q 8).Inside 1 (87/50) := by
    simpa using outside 8 (1,87/50) (by norm_num [outsidePoints])
  have leftFar : (q 8).Inside 1 (14/5) :=
    C981CompletionWallAdvance.point (q 8) (side 8) (box 8) leftMarker leftHigh leftMissing
      (foreign 8 1 (by decide) _ _ (by simpa using inside 1 (19/25,187/100) (by norm_num [insidePoints])))
      (foreign 8 7 (by decide) _ _ nMarker)
  have nNorth : (q 7).Inside 2 (113/50) := by
    simpa using inside 7 (2,113/50) (by norm_num [insidePoints])
  have nUpper : (q 7).Inside (87/50) 3 := by
    simpa using inside 7 (87/50,3) (by norm_num [insidePoints])
  have topMarker : (q 11).Inside 2 (1543/500) := by
    simpa using inside 11 (2,1543/500) (by norm_num [insidePoints])
  have topNear : (q 11).Inside (12/5) 3 := by
    simpa using inside 11 (12/5,3) (by norm_num [insidePoints])
  have topLow : (q 11).Inside (113/50) 3 := by
    simpa using inside 11 (113/50,3) (by norm_num [insidePoints])
  let w := C981CompletionCharts.shiftedTop (q 11)
  let n := C981CompletionCharts.shiftedTop (q 7)
  have north : w.Inside 0 (43/500) := by
    apply (C981CompletionCharts.inside_shiftedTop _ _ _).mpr
    convert topMarker using 1 <;> norm_num
  have east : w.Inside (2/5) 0 := by
    apply (C981CompletionCharts.inside_shiftedTop _ _ _).mpr
    convert topNear using 1 <;> norm_num
  have topFar : (q 11).Inside (273/100) 3 := by
    by_cases origin : (q 11).Inside 2 3
    · have nF : n.Inside (-(13/50)) 0 := by
        apply (C981CompletionCharts.inside_shiftedTop _ _ _).mpr
        convert nUpper using 1 <;> norm_num
      have nA : n.Inside 0 (-(37/50)) := by
        apply (C981CompletionCharts.inside_shiftedTop _ _ _).mpr
        convert nNorth using 1 <;> norm_num
      have nM : n.Inside (-(7/20)) (-(13/20)) := by
        apply (C981CompletionCharts.inside_shiftedTop _ _ _).mpr
        convert nMarker using 1 <;> norm_num
      have nO : ¬ n.Inside 0 0 := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 7 11 (by decide) _ _ origin h
      have nZ : ¬ n.Inside (-(2/5)) 0 := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        have missing : ¬ (q 7).Inside (8/5) 3 := by
          simpa using outside 7 (8/5,3) (by norm_num [outsidePoints])
        exact missing h
      have nB : ¬ n.Inside (-(13/50)) (-1) := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        have missing : ¬ (q 7).Inside (87/50) 2 := by
          simpa using outside 7 (87/50,2) (by norm_num [outsidePoints])
        exact missing h
      have nR : ¬ n.Inside (7/20) (-(13/20)) := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 7 6 (by decide) _ _ bMarker h
      have nL : ¬ n.Inside (-1) (-(1/5)) := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 7 8 (by decide) _ _ leftFar h
      have tip := C981CompletionTopReach.central_tip n (side 7) nF nA nM nO nZ nB nR nL
      have wL : ¬ w.Inside (-(3/100)) 0 := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        have h' := (C981CompletionCharts.inside_shiftedTop _ _ _).mp tip
        exact foreign 11 7 (by decide) _ _ h' h
      have wA : ¬ w.Inside 0 (-(37/50)) := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 11 7 (by decide) _ _ nNorth h
      have point := C981CompletionTopReach.foreign_tip w (side 11)
        (C981CompletionCharts.shiftedTop_wall _ (box 11)) north east wL wA
      have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
      norm_num at h
      exact h
    · have wO : ¬ w.Inside 0 0 := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact origin h
      have point := C981CompletionTopReach.origin_alternative w (side 11)
        (C981CompletionCharts.shiftedTop_wall _ (box 11)) north east wO
      have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
      norm_num at h
      obtain ⟨a,b,c,d⟩ := h
      obtain ⟨e,f,g,h⟩ := topNear
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d,e,f,g,h]
  exact ending q side same inside
    (by simpa using outside 5 (33/20,33/20) (by norm_num [outsidePoints])) topFar apart

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  let q := owners p
  have aux (i : Fin 12) : AuxExact (q i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [q,owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ (checked.2 i P member)
  exact geometry q (fun i => owners_side_gt p i)
    (fun i j => (p.congruent _).trans (p.congruent _).symm)
    (fun i => owners_contained p i) inside outside
    (fun i j different => owners_disjoint p hf i j different)

def coveredIds : List Nat := [59,105,108]
theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) := by decide +kernel
theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i member)

#print axioms covered_excluded
end N12Compact.C981CompletionShortWallRows
