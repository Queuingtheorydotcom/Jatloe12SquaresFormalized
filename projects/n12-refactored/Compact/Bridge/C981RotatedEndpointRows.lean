import Compact.Bridge.C981EndpointRows

/-! Coordinate exchange exposes the same complete endpoint ending at the
other two available central markers. The original representatives, owners,
queries and square orientations are unchanged. -/
namespace N12Compact.C981RotatedEndpointRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def east : C981MidpointRows.Data := ⟨⟨true,false,false⟩,![6,5,9,11]⟩
def southEast : C981MidpointRows.Data := ⟨⟨true,false,true⟩,![5,6,11,9]⟩

def eastIds : List Nat := [75,76,79,80,81,82,83,84,86,87,88,89,90,91,92,102]
def southEastIds : List Nat := [15,16,48,61,62,63,64,65,74]

theorem east_checked : ∀ i ∈ eastIds,
    east.Check (representativeVectors[i]!) := by decide +kernel

theorem southEast_checked : ∀ i ∈ southEastIds,
    southEast.Check (representativeVectors[i]!) := by decide +kernel

def additionalIds : List Nat :=
  (eastIds ++ southEastIds).filter (fun i => !(decide (i ∈ C981EndpointRows.coveredIds)))

def coveredIds : List Nat := C981EndpointRows.coveredIds ++ additionalIds

/-- The complete 46-entry union, including the perpendicular-span case 77.
Each conclusion excludes an actual original ownership vector. -/
theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := by
  rcases List.mem_append.mp hi with old | added
  · exact C981EndpointRows.covered_excluded i old
  · have rotated : i ∈ eastIds ++ southEastIds := (List.mem_filter.mp added).1
    rcases List.mem_append.mp rotated with eastCase | southCase
    · exact C981MidpointRows.excludes east _ (east_checked i eastCase)
    · exact C981MidpointRows.excludes southEast _ (southEast_checked i southCase)

def newlyResidualIds : List Nat := [45,46,47,49,67,68,72,75,76,77,78,79,96]
def pendingResidualIds : List Nat :=
  Case981.remainingIndices.filter (fun i => !(decide (i ∈ coveredIds)))

theorem additional_literal : additionalIds =
    [79,80,81,86,87,89,90,91,15,16,48,61,62,63,64,65,74] := by decide +kernel
theorem covered_count : coveredIds.length = 46 := by decide +kernel
theorem residual_difference :
    Case981.remainingIndices.filter (fun i => decide (i ∈ coveredIds)) = newlyResidualIds := by
  decide +kernel
theorem pending_residual_count : pendingResidualIds.length = 42 := by decide +kernel

#print axioms covered_excluded
end N12Compact.C981RotatedEndpointRows
