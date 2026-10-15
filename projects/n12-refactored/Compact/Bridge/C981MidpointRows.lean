import Compact.Geometry.EndpointRowTemplate
import Compact.Cases.C981

/-! The original C981 packing entry for the strengthened endpoint-row argument.
The finite data chooses actual owners and a spatial symmetry. Every inside
and outside premise is checked against the unchanged original query tables;
no propagated pose domain or numerical trace appears in this theorem. -/
namespace N12Compact.C981MidpointRows

open S12 S12Pilot S12Completion.C981 FourSquareAnchors
set_option Elab.async false

structure Data where
  transform : Transform
  roles : Fin 4 → Fin 12

def insidePoints (d : Data) : Fin 4 → List (ℚ × ℚ)
  | 0 => [(2,113/50),(113/50,2),(47/20,47/20)]
  | 1 => [(33/20,47/20),(87/50,2),(8/5,3)]
  | 2 => [(1,12/5)]
  | _ => [(1543/500,2),(3,12/5)]

def outsidePoints : Fin 4 → List (ℚ × ℚ)
  | 0 => [(33/20,33/20),(47/20,33/20)]
  | 3 => [(3,87/50)]
  | _ => []

def Data.Check (d : Data) (v : List (Finset Nat)) : Prop :=
  Function.Injective d.roles ∧
  (∀ i, ∀ P ∈ insidePoints d i, d.transform.applyRat P ∈
    queryInsidePoints (ownerMasks (d.roles i)) 2 (v[(d.roles i).val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, d.transform.applyRat P ∈
    queryOutsidePoints (ownerMasks (d.roles i)) 2 (v[(d.roles i).val]!))

instance (d : Data) (v : List (Finset Nat)) : Decidable (d.Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem close {q : OpenSquare} {x y : ℝ} (hp : q.Inside x y) :
    ClosedInside q x y := ⟨hp.1.le,hp.2.1.le,hp.2.2.1.le,hp.2.2.2.le⟩

/-- A whole original representative exclusion, conditional only on the
finite memberships of its actual data, not on any new geometry premise. -/
theorem excludes (d : Data) (v : List (Finset Nat)) (checked : d.Check v) :
    ExcludesVector v := by
  intro p hf hv
  obtain ⟨injective,hin,hout⟩ := checked
  let q : Fin 4 → OpenSquare := fun i => d.transform.pull (owners p (d.roles i))
  have aux (i : Fin 4) : AuxExact (owners p (d.roles i)) 2 (v[(d.roles i).val]!) := by
    have he := ownership_entry_at p v hv (d.roles i)
    simpa only [owners,he] using
      nat_combined_exact p (ownerIndex p (ownerMasks (d.roles i)))
  have inside (i : Fin 4) (P : ℚ × ℚ) (hp : P ∈ insidePoints d i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform d.transform (owners p (d.roles i)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (d.roles i))
      (owners_side_le p (d.roles i)) (owners_contained p (d.roles i))
      (owners_markers p hf (d.roles i)) (aux i) _ (hin i P hp)
  have outside (i : Fin 4) (P : ℚ × ℚ) (hp : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 := by
    intro hq
    exact query_outside_sound _ 2 _ _ (owners_markers p hf (d.roles i))
      (aux i) _ (hout i P hp) ((rat_inside_transform _ _ _).mp hq)
  have apart (i j : Fin 4) (hne : i ≠ j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y hp
    exact owners_disjoint p hf (d.roles i) (d.roles j)
      (fun he => hne (injective he)) _ _
      ⟨(inside_pull _ _ _ _).mp hp.1,(inside_pull _ _ _ _).mp hp.2⟩
  have side (i : Fin 4) : 1 < (q i).side := by
    simpa only [q,pull_same_side] using owners_side_gt p (d.roles i)
  have box (i : Fin 4) : InsideContainer (q i) :=
    container_transform _ _ (owners_contained p (d.roles i))
  apply EndpointRowTemplate.impossible (q 0) (q 1) (q 2) (q 3)
  refine {
    aSide := side 0, bSide := side 1, rSide := side 3
    rBox := box 3
    aP := ?_, aQ := ?_, aT := ?_, aF := ?_, aG := ?_
    bMarker := ?_, bLow := ?_, bHigh := ?_, lQ := ?_
    rP := ?_, rQ := ?_, rMissingLow := ?_
    ab := apart 0 1 (by decide), ar := apart 0 3 (by decide)
    bl := apart 1 2 (by decide) }
  · simpa using close (inside 0 (2,113/50) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (113/50,2) (by norm_num [insidePoints]))
  · simpa using close (inside 0 (47/20,47/20) (by norm_num [insidePoints]))
  · simpa using outside 0 (33/20,33/20) (by norm_num [outsidePoints])
  · simpa using outside 0 (47/20,33/20) (by norm_num [outsidePoints])
  · simpa using close (inside 1 (33/20,47/20) (by norm_num [insidePoints]))
  · simpa using inside 1 (87/50,2) (by norm_num [insidePoints])
  · simpa using inside 1 (8/5,3) (by norm_num [insidePoints])
  · simpa using close (inside 2 (1,12/5) (by norm_num [insidePoints]))
  · simpa using close (inside 3 (1543/500,2) (by norm_num [insidePoints]))
  · simpa using close (inside 3 (3,12/5) (by norm_num [insidePoints]))
  · simpa using outside 3 (3,87/50) (by norm_num [outsidePoints])

def northEast : Data := ⟨⟨false,false,false⟩,![6,7,8,10]⟩
def northWest : Data := ⟨⟨false,true,false⟩,![7,6,10,8]⟩

def northEastIds : List Nat := [75,78,82,84,85,88,92,96,97,100,102]
def northWestIds : List Nat := [9,10,11,12,13,14,17,18,45,46,47,49,67,68,72]
def coveredIds : List Nat := northEastIds ++ northWestIds

theorem northEast_checked : ∀ i ∈ northEastIds,
    northEast.Check (representativeVectors[i]!) := by decide +kernel

theorem northWest_checked : ∀ i ∈ northWestIds,
    northWest.Check (representativeVectors[i]!) := by decide +kernel

/-- The 26 literal original representatives, including ten formerly residual
obligations. This does not claim catalogue coverage or exclude the whole case. -/
theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := by
  rcases List.mem_append.mp hi with ne | nw
  · exact excludes northEast _ (northEast_checked i ne)
  · exact excludes northWest _ (northWest_checked i nw)

def newlyResidualIds : List Nat := [45,46,47,49,67,68,72,75,78,96]
def pendingResidualIds : List Nat :=
  Case981.remainingIndices.filter (fun i => !(decide (i ∈ coveredIds)))

theorem covered_count : coveredIds.length = 26 := by decide +kernel
theorem residual_difference :
    Case981.remainingIndices.filter (fun i => decide (i ∈ coveredIds)) = newlyResidualIds := by
  decide +kernel
theorem pending_residual_count : pendingResidualIds.length = 45 := by decide +kernel

#print axioms covered_excluded
end N12Compact.C981MidpointRows
