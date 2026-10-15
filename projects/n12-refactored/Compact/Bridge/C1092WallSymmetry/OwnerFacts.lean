import Compact.Bridge.C1092WallSymmetry.Actions

/-! Finite exact-owner identities, separated from continuous transport.
The owner identity is partitioned before kernel reduction. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

namespace FiniteFacts

/-- Each closed kernel check has one symmetry and one original owner. -/
theorem owner_marker_transport : ∀ a b c : Bool, ∀ i : Fin 12, ∀ j : Marker,
    (Transform.markerAction ⟨a,b,c⟩ j ∈
      maskSupport (ownerCode (ownerAction ⟨a,b,c⟩ i))) ↔
    j ∈ maskSupport (ownerCode i) := by
  intro a b c i
  cases a <;> cases b <;> cases c <;> fin_cases i <;> decide +kernel

theorem owner_code_candidate (i : Fin 12) : ownerCode i ∈ candidateMasks := by
  fin_cases i <;> decide +kernel

theorem family_enumerated : ∀ m ∈ family, ∃ i : Fin 12, ownerCode i = m := by
  decide +kernel

end FiniteFacts

end N12Compact.C1092WallSymmetry
