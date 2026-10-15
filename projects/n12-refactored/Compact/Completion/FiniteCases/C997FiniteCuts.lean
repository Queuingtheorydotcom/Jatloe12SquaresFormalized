import Compact.Completion.FiniteCases.C997Domains

/-! Each ownership implication checks one small literal list, independently
of the actual-family budgets, transformed-domain construction and certificate
refutation tables. The packing soundness stays in C997Domains. -/
namespace N12Compact.FiniteCases.C997FiniteCuts
open C997Domains
set_option Elab.async false

theorem southwest_has_two : ∀ s∈southwestAllowed, 2∈s := by decide +kernel

theorem bottom_points : ∀ s∈bottomAllowed, 2∉s → 6∈s ∧ 15∈s := by decide +kernel

theorem southwest_has_four : ∀ s∈southwestCentralAllowed, 0∉s → 2∉s → 6∉s → 4∈s := by decide +kernel

theorem top_points : ∀ s∈topAllowed, 3∉s → 7∈s ∧ 17∈s := by decide +kernel

theorem southeast_has_eight : ∀ s∈southeastAllowed, 4∉s → 6∉s → 8∈s := by decide +kernel

theorem right_points : ∀ s∈rightAllowed, 8∉s → 7∉s → 9∈s ∧ 19∈s := by decide +kernel

theorem northeast_points : ∀ s∈northeastAllowed, 7∉s → 9∉s → 17∉s → 19∉s → 5∈s ∧ 16∈s := by decide +kernel

theorem southeast_has_eighteen : ∀ s∈southeastAllowed, 15∉s → 16∉s → 18∈s := by decide +kernel

end N12Compact.FiniteCases.C997FiniteCuts
