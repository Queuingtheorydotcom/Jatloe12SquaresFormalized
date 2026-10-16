import Compact.Completion.C981.ShortWallRows
import Compact.Completion.C981.ShallowWall

/-! Original representative 71. Its northwest central square really
owns (1.6,3), so this entrance uses the full actual left-wall segment and
the circular cap instead of the isolated omission used in the other rows. -/
namespace N12Compact.C981CompletionShortWall71

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def outsidePoints : Fin 12 → List (ℚ × ℚ)
  | 5 => [(33/20,33/20)]
  | 7 => [(87/50,2)]
  | 8 => [(1,87/50)]
  | _ => []

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ C981CompletionShortWallRows.insidePoints i,
    P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  let q := owners p
  have aux (i : Fin 12) : AuxExact (q i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [q,owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ)
      (member : P ∈ C981CompletionShortWallRows.insidePoints i) :
      (q i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ (checked.2 i P member)
  have foreign (i j : Fin 12) (different : i ≠ j) (x y : ℝ)
      (point : (q j).Inside x y) : ¬ (q i).Inside x y := by
    intro own
    exact owners_disjoint p hf i j different x y ⟨own,point⟩
  have side (i : Fin 12) : 1 < (q i).side := owners_side_gt p i
  have box (i : Fin 12) : InsideContainer (q i) := owners_contained p i
  have leftMarker : (q 8).Inside (457/500) 2 := by
    simpa using inside 8 (457/500,2) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have leftLow : (q 8).Inside 1 (113/50) := by
    simpa using inside 8 (1,113/50) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have leftHigh : (q 8).Inside 1 (12/5) := by
    simpa using inside 8 (1,12/5) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have nMarker : (q 7).Inside (33/20) (47/20) := by
    simpa using inside 7 (33/20,47/20) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have leftMissing : ¬ (q 8).Inside 1 (87/50) := by
    simpa using outside 8 (1,87/50) (by norm_num [outsidePoints])
  have cornerPoint : (q 1).Inside (19/25) (187/100) := by
    simpa using inside 1 (19/25,187/100)
      (by norm_num [C981CompletionShortWallRows.insidePoints])
  have leftFar : (q 8).Inside 1 (14/5) :=
    C981CompletionWallAdvance.point (q 8) (side 8) (box 8) leftMarker leftHigh leftMissing
      (foreign 8 1 (by decide) _ _ cornerPoint)
      (foreign 8 7 (by decide) _ _ nMarker)
  have leftSegment (y : ℝ) (lo : 113/50 ≤ y) (hi : y ≤ 14/5) : (q 8).Inside 1 y := by
    let t := (y-113/50)/(14/5-113/50)
    have tn : 0 ≤ t := div_nonneg (by linarith only [lo]) (by norm_num)
    have tu : t ≤ 1 := (div_le_iff₀ (by norm_num : (0:ℝ) < 14/5-113/50)).mpr
      (by linarith only [hi])
    have point := inside_segment (q 8) 1 (113/50) 1 (14/5) t leftLow leftFar tn tu
    convert point using 1 <;> dsimp [t] <;> ring
  have nNorth : (q 7).Inside 2 (113/50) := by
    simpa using inside 7 (2,113/50) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have nUpper : (q 7).Inside (87/50) 3 := by
    simpa using inside 7 (87/50,3) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have topMarker : (q 11).Inside 2 (1543/500) := by
    simpa using inside 11 (2,1543/500) (by norm_num [C981CompletionShortWallRows.insidePoints])
  have topNear : (q 11).Inside (12/5) 3 := by
    simpa using inside 11 (12/5,3) (by norm_num [C981CompletionShortWallRows.insidePoints])
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
      have nO : ¬ n.Inside 0 0 := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 7 11 (by decide) _ _ origin h
      have nB : ¬ n.Inside (-(13/50)) (-1) := by
        intro point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        have missing : ¬ (q 7).Inside (87/50) 2 := by
          simpa using outside 7 (87/50,2) (by norm_num [outsidePoints])
        exact missing h
      have nSegment : ∀ y : ℝ, -(37/50) ≤ y → y ≤ -(1/5) → ¬ n.Inside (-1) y := by
        intro y lo hi point
        have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp point
        norm_num at h
        exact foreign 7 8 (by decide) _ _
          (leftSegment (3+y) (by linarith only [lo]) (by linarith only [hi])) h
      obtain ⟨r,hc,canon,shape,equivalent,_⟩ := ClosedFrames.canonical_frame n
      have rSide : 1 < r.side := by
        simpa only [shape,n,C981CompletionCharts.shiftedTop_side] using side 7
      have rF := (equivalent _ _).mpr nF
      have rA := (equivalent _ _).mpr nA
      have rB : ¬ r.Inside (-(13/50)) (-1) := fun h => nB ((equivalent _ _).mp h)
      have point : w.Inside (73/100) 0 := by
        by_cases sign : 0 ≤ r.s
        · have rSegment : ∀ y : ℝ, -(37/50) ≤ y → y ≤ -(1/5) → ¬ r.Inside (-1) y := by
            intro y lo hi h
            exact nSegment y lo hi ((equivalent _ _).mp h)
          have tip := C981CompletionShallowCap.positive_tip r rSide hc sign
            (by simpa only [abs_of_nonneg sign] using canon) rF rA
            (fun h => nO ((equivalent _ _).mp h)) rB rSegment
          have wL : ¬ w.Inside (-(3/100)) 0 := by
            intro h
            exact foreign 11 7 (by decide) _ _
              ((C981CompletionCharts.inside_shiftedTop _ _ _).mp ((equivalent _ _).mp tip))
              ((C981CompletionCharts.inside_shiftedTop _ _ _).mp h)
          have wA : ¬ w.Inside 0 (-(37/50)) := by
            intro h
            have original := (C981CompletionCharts.inside_shiftedTop _ _ _).mp h
            norm_num at original
            exact foreign 11 7 (by decide) _ _ nNorth original
          exact C981CompletionTopReach.foreign_tip w (side 11)
            (C981CompletionCharts.shiftedTop_wall _ (box 11)) north east wL wA
        · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge sign)
          have region := C981CompletionShallowCap.negative_cap r rSide hc negative
            (by simpa only [abs_of_nonpos negative] using canon) rF rA rB
          have avoid : ∀ x y, C981CompletionShallowCap.Cap x y → ¬ w.Inside x y := by
            intro x y cap h
            exact foreign 11 7 (by decide) _ _
              ((C981CompletionCharts.inside_shiftedTop _ _ _).mp ((equivalent _ _).mp (region x y cap)))
              ((C981CompletionCharts.inside_shiftedTop _ _ _).mp h)
          exact C981CompletionShallowWall.point w (side 11)
            (C981CompletionCharts.shiftedTop_wall _ (box 11)) north east avoid
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
  exact C981CompletionShortWallRows.ending q side
    (fun i j => (p.congruent _).trans (p.congruent _).symm) inside
    (by simpa using outside 5 (33/20,33/20) (by norm_num [outsidePoints])) topFar
    (fun i j different => owners_disjoint p hf i j different)

theorem checked : Check (representativeVectors[71]!) := by decide +kernel
theorem representative71_excluded : ExcludesVector (representativeVectors[71]!) := excludes _ checked

#print axioms representative71_excluded
end N12Compact.C981CompletionShortWall71
