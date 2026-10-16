import Completion.Cases.C981.VectorData
import Compact.Geometry.DiagonalOuterPoint

/-! Original C981 auxiliary ownership {9,17} gives the two diagonal endpoints
and misses both inner and outer pairs. The entire vector is excluded by one
original owner's square. No marker seed, side upper bound, containment, or
other-owner separation is used. -/
namespace N12Compact.C981DiagonalOuter

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def Check (v : List (Finset Nat)) : Prop :=
  17 ∈ v[6]! ∧ 9 ∈ v[6]! ∧ 5 ∉ v[6]! ∧ 16 ∉ v[6]! ∧
    7 ∉ v[6]! ∧ 19 ∉ v[6]!

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p _ hv
  obtain ⟨ownedTop,ownedRight,missingLeft,missingLow,missingTop,missingRight⟩ := checked
  let q := owners p 6
  have aux : AuxExact q 2 (v[6]!) := by
    have he := ownership_entry_at p v hv 6
    change natCombinedOwners p (ownerIndex p (ownerMasks 6)) = v[6]! at he
    simpa only [q,owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks 6))
  have top : q.Inside (113/50) 3 := by
    have h := (aux 17 (by decide)).mpr ownedTop
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have right : q.Inside 3 (113/50) := by
    have h := (aux 9 (by decide)).mpr ownedRight
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have leftMissing : ¬ q.Inside 2 (113/50) := by
    have h := mt (aux 5 (by decide)).mp missingLeft
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have lowMissing : ¬ q.Inside (113/50) 2 := by
    have h := mt (aux 16 (by decide)).mp missingLow
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have topMissing : ¬ q.Inside (12/5) 3 := by
    have h := mt (aux 7 (by decide)).mp missingTop
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have rightMissing : ¬ q.Inside 3 (12/5) := by
    have h := mt (aux 19 (by decide)).mp missingRight
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  exact DiagonalOuterPoint.impossible q (owners_side_gt p 6)
    top right leftMissing lowMissing topMissing rightMissing

/-- These are additional original-vector endings. Representative 116 also
satisfies Check, but already has a connected compact proof. -/
def coveredIds : List Nat := [7,110]

theorem covered_checked : ∀ i ∈ coveredIds,
    Check (representativeVectors[i]!) := by decide +kernel

theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) :=
  excludes _ (covered_checked i hi)

#print axioms covered_excluded
end N12Compact.C981DiagonalOuter
