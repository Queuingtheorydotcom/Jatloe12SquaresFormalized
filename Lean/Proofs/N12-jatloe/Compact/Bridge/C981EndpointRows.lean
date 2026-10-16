import Compact.Bridge.C981MidpointRows

/-! Two perpendicular spans close the cases in which the right wall owns
the lower point. Every premise is still a literal original-owner fact. -/
namespace N12Compact.C981EndpointRows

open S12 S12Pilot S12Completion.C981 FourSquareAnchors
set_option Elab.async false

def roles : Fin 5 → Fin 12 := ![6,7,5,8,9]

def insidePoints : Fin 5 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(87/50,2),(8/5,3)]
  | 2 => [(2,87/50),(3,8/5)]
  | 3 => [(1,12/5)]
  | _ => [(12/5,1)]

def outsidePoints : List (ℚ × ℚ) :=
  [(33/20,33/20),(47/20,33/20),(33/20,47/20),(3,12/5),(12/5,3)]

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, P ∈
    queryInsidePoints (ownerMasks (roles i)) 2 (v[(roles i).val]!)) ∧
  (∀ P ∈ outsidePoints, P ∈
    queryOutsidePoints (ownerMasks (roles 0)) 2 (v[(roles 0).val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem close {q : OpenSquare} {x y : ℝ} (hp : q.Inside x y) :
    ClosedInside q x y := ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  obtain ⟨hin,hout⟩ := checked
  let q : Fin 5 → OpenSquare := fun i => owners p (roles i)
  have aux (i : Fin 5) : AuxExact (owners p (roles i)) 2 (v[(roles i).val]!) := by
    have he := ownership_entry_at p v hv (roles i)
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks (roles i)))
  have inside (i : Fin 5) (P : ℚ × ℚ) (hp : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p (roles i))
      (owners_side_le p (roles i)) (owners_contained p (roles i))
      (owners_markers p hf (roles i)) (aux i) _ (hin i P hp)
  have outside (P : ℚ × ℚ) (hp : P ∈ outsidePoints) :
      ¬ (q 0).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf (roles 0))
      (aux 0) _ (hout P hp)
  have injective : Function.Injective roles := by decide +kernel
  have apart (i j : Fin 5) (hne : i ≠ j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) :=
    owners_disjoint p hf (roles i) (roles j) (fun he => hne (injective he))
  apply EndpointRowTemplate.dual_impossible (q 0) (q 1) (q 2) (q 3) (q 4)
  refine {
    aSide := owners_side_gt p (roles 0), bSide := owners_side_gt p (roles 1)
    cSide := owners_side_gt p (roles 2)
    aP := ?_, aQ := ?_, aT := ?_, aF := ?_, aG := ?_, aB := ?_, aR := ?_, aTop := ?_
    bLow := ?_, bHigh := ?_, cLow := ?_, cHigh := ?_, lQ := ?_, dQ := ?_
    ab := apart 0 1 (by decide), ac := apart 0 2 (by decide)
    bl := apart 1 3 (by decide), cd := apart 2 4 (by decide) }
  · simpa using close (inside 0 (2,113/50) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (113/50,2) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (47/20,47/20) (by norm_num [insidePoints]))
  · simpa using outside (33/20,33/20) (by norm_num [outsidePoints])
  · simpa using outside (47/20,33/20) (by norm_num [outsidePoints])
  · simpa using outside (33/20,47/20) (by norm_num [outsidePoints])
  · simpa using outside (3,12/5) (by norm_num [outsidePoints])
  · simpa using outside (12/5,3) (by norm_num [outsidePoints])
  · simpa using inside 1 (87/50,2) (by norm_num [insidePoints])
  · simpa using inside 1 (8/5,3) (by norm_num [insidePoints])
  · simpa using inside 2 (2,87/50) (by norm_num [insidePoints])
  · simpa using inside 2 (3,8/5) (by norm_num [insidePoints])
  · simpa using close (inside 3 (1,12/5) (by norm_num [insidePoints]))
  · simpa using close (inside 4 (12/5,1) (by norm_num [insidePoints]))

def additionalIds : List Nat := [76,77,83]
def coveredIds : List Nat := C981MidpointRows.coveredIds ++ additionalIds

theorem additional_checked : ∀ i ∈ additionalIds,
    Check (representativeVectors[i]!) := by decide +kernel

/-- All 29 replacements have whole original-vector conclusions. Full C981
still also requires every other representative and catalogue coverage. -/
theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := by
  rcases List.mem_append.mp hi with old | added
  · exact C981MidpointRows.covered_excluded i old
  · exact excludes _ (additional_checked i added)

def newlyResidualIds : List Nat := [45,46,47,49,67,68,72,75,76,77,78,96]
def pendingResidualIds : List Nat :=
  Case981.remainingIndices.filter (fun i => !(decide (i ∈ coveredIds)))

theorem covered_count : coveredIds.length = 29 := by decide +kernel
theorem residual_difference :
    Case981.remainingIndices.filter (fun i => decide (i ∈ coveredIds)) = newlyResidualIds := by
  decide +kernel
theorem pending_residual_count : pendingResidualIds.length = 43 := by decide +kernel

#print axioms covered_excluded
end N12Compact.C981EndpointRows
