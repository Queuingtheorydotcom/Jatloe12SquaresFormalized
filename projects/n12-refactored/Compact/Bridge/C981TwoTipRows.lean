import Compact.Geometry.C981TwoTip
import Completion.Cases.C981.VectorData
import S12.TransformFacts

/-! Eleven whole original C981 representative-vector exclusions.  Each
placement moves the two actual owners together.  The finite checks concern
only literal marker/auxiliary memberships and absences; no pose enclosures,
orientation discretization, new assumptions or native certificates occur. -/
namespace N12Compact.C981TwoTipRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

structure Data where
  transform : Transform
  roles : Fin 2 → Fin 12

def insidePoints : Fin 2 → List (ℚ × ℚ)
  | 0 => [(47/20,47/20),(12/5,3)]
  | _ => [(113/50,2),(3,12/5)]

def outsidePoints : Fin 2 → List (ℚ × ℚ)
  | 0 => [(87/50,3)]
  | _ => [(3,87/50)]

def Data.Check (d : Data) (v : List (Finset Nat)) : Prop :=
  Function.Injective d.roles ∧
  (∀ i, ∀ P ∈ insidePoints i, d.transform.applyRat P ∈
    queryInsidePoints (ownerMasks (d.roles i)) 2 (v[(d.roles i).val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, d.transform.applyRat P ∈
    queryOutsidePoints (ownerMasks (d.roles i)) 2 (v[(d.roles i).val]!))

instance (d : Data) (v : List (Finset Nat)) : Decidable (d.Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Membership checking discharges all premises in the actual original
packing.  The conclusion is the unchanged whole-vector contract. -/
theorem excludes (d : Data) (v : List (Finset Nat)) (checked : d.Check v) :
    ExcludesVector v := by
  intro p hf hv
  obtain ⟨injective,hin,hout⟩ := checked
  let q : Fin 2 → OpenSquare := fun i => d.transform.pull (owners p (d.roles i))
  have aux (i : Fin 2) : AuxExact (owners p (d.roles i)) 2 (v[(d.roles i).val]!) := by
    have he := ownership_entry_at p v hv (d.roles i)
    simpa only [owners,he] using
      nat_combined_exact p (ownerIndex p (ownerMasks (d.roles i)))
  have inside (i : Fin 2) (P : ℚ × ℚ) (hp : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform d.transform (owners p (d.roles i)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (d.roles i))
      (owners_side_le p (d.roles i)) (owners_contained p (d.roles i))
      (owners_markers p hf (d.roles i)) (aux i) _ (hin i P hp)
  have outside (i : Fin 2) (P : ℚ × ℚ) (hp : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 := by
    intro hq
    exact query_outside_sound _ 2 _ _ (owners_markers p hf (d.roles i))
      (aux i) _ (hout i P hp) ((rat_inside_transform _ _ _).mp hq)
  have apart : ∀ x y, ¬ ((q 0).Inside x y ∧ (q 1).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (d.roles 0) (d.roles 1)
      (fun he => (by decide : (0 : Fin 2) ≠ 1) (injective he)) _ _
      ⟨(inside_pull _ _ _ _).mp h.1,(inside_pull _ _ _ _).mp h.2⟩
  have side (i : Fin 2) : 1 < (q i).side := by
    simpa only [q,pull_same_side] using owners_side_gt p (d.roles i)
  apply C981TwoTip.impossible (q 0) (q 1) (side 0) (side 1)
  · simpa using inside 0 (47/20,47/20) (by norm_num [insidePoints])
  · simpa using inside 0 (12/5,3) (by norm_num [insidePoints])
  · simpa using outside 0 (87/50,3) (by norm_num [outsidePoints])
  · simpa using inside 1 (113/50,2) (by norm_num [insidePoints])
  · simpa using inside 1 (3,12/5) (by norm_num [insidePoints])
  · simpa using outside 1 (3,87/50) (by norm_num [outsidePoints])
  · exact apart

/-- Identity placement at the northeast central and right wall owners. -/
def northEast : Data := ⟨⟨false,false,false⟩,![6,10]⟩
/-- Reflect the whole two-owner configuration in x = 2. -/
def northWest : Data := ⟨⟨false,true,false⟩,![7,8]⟩
/-- The map (x,y) ↦ (y,4-x), applied to both actual owners. -/
def southEast : Data := ⟨⟨true,false,true⟩,![5,9]⟩

def northEastIds : List Nat := [25,31,40,70]
def northWestIds : List Nat := [32,33,38,57,99]
def southEastIds : List Nat := [94,95]
def coveredIds : List Nat := (northEastIds ++ northWestIds) ++ southEastIds

theorem northEast_checked : ∀ i ∈ northEastIds,
    northEast.Check (representativeVectors[i]!) := by decide +kernel

theorem northWest_checked : ∀ i ∈ northWestIds,
    northWest.Check (representativeVectors[i]!) := by decide +kernel

theorem southEast_checked : ∀ i ∈ southEastIds,
    southEast.Check (representativeVectors[i]!) := by decide +kernel

/-- All eleven full-vector conclusions, with every side/orientation/contact
possibility retained.  The remaining C981 vectors are separate obligations. -/
theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := by
  rcases List.mem_append.mp hi with north | south
  · rcases List.mem_append.mp north with east | west
    · exact excludes northEast _ (northEast_checked i east)
    · exact excludes northWest _ (northWest_checked i west)
  · exact excludes southEast _ (southEast_checked i south)

theorem covered_count : coveredIds.length = 11 := by decide +kernel

#print axioms covered_excluded
end N12Compact.C981TwoTipRows
