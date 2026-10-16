import Compact.Assembly.RowIdentity

namespace S12Completion.C977

/-- The complete marker family of retained case 977. -/
def family : Finset Nat :=
  {1, 2, 12, 48, 192, 256, 512, 2048, 4096, 8192, 16384, 32768}

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 508).originalId = 977 ∧
    (N12Compact.RowIdentity.rowAt 508).groups = family := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All retained rows with historical ID 977 have this family. -/
theorem row_family :
    ∀ r ∈ S12.retainedRows, r.originalId = 977 → r.groups = family := by
  exact N12Compact.RowIdentity.family_at 508 977 family lookup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- This family occurs in the retained table, so the case contract is nonvacuous. -/
theorem family_retained :
    ∃ r ∈ S12.retainedRows, r.originalId = 977 ∧ r.groups = family := by
  refine ⟨N12Compact.RowIdentity.rowAt 508, ?_, lookup.1, lookup.2⟩
  apply List.mem_filter.mpr
  refine ⟨N12Compact.RowIdentity.rowAt_mem 508, decide_eq_true ?_⟩
  rw [lookup.1]
  decide +kernel

/-- The case contract is precisely exclusion of the entire marker family. -/
theorem excludes_case_iff :
    ExcludesCase 977 ↔ ExcludesFamily family := by
  constructor
  · intro h
    obtain ⟨r, hr, hid, hf⟩ := family_retained
    simpa only [hf] using h r hr hid
  · intro h r hr hid
    simpa only [row_family r hr hid] using h

end S12Completion.C977
