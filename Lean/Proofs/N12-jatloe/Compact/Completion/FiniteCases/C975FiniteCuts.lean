import Compact.Completion.FiniteCases.C975Domains

/-! Each cut reads one literal list, retaining the authentic ordinary
two-point allowances on both grids. No complete packing search is used. -/
namespace N12Compact.FiniteCases.C975FiniteCuts
open S12 C975Domains
set_option Elab.async false

theorem southwest : ∀ s∈C997Domains.southwestAllowed, 2∈s ∧ 12∈s := by
  decide +kernel

theorem leftSingleton : ∀ s∈leftSingletonAllowed, 0∈s ∧ 10∈s := by
  decide +kernel

theorem bottom : ∀ s∈C997Domains.bottomAllowed, 2∉s → 6∈s ∧ 15∈s := by
  decide +kernel

theorem southwestCentral : ∀ s∈C997Domains.southwestCentralAllowed,
    0∉s → 2∉s → 10∉s → 12∉s → 4∈s ∧ 13∈s := by
  decide +kernel

theorem leftWall : ∀ s∈leftAllowed, 0∉s → 13∉s → 1∈s ∧ 11∈s := by
  decide +kernel

theorem southeast : ∀ s∈C997Domains.southeastAllowed,
    4∉s → 6∉s → 15∉s → 8∈s ∧ (16∈s ∨ 18∈s) := by
  decide +kernel

theorem rightWall : ∀ s∈C997Domains.rightAllowed, 8∉s → 9∈s ∧ 19∈s := by
  decide +kernel

theorem top : ∀ s∈topGAllowed, 1∉s → 3∉s → 4∈s := by decide +kernel

theorem northeast : ∀ s∈C997Domains.northeastAllowed,
    9∉s → 13∉s → 14∉s → 19∉s → (5∈s ∨ 7∈s) ∧ (16∈s ∨ 17∈s) := by
  decide +kernel

end N12Compact.FiniteCases.C975FiniteCuts
