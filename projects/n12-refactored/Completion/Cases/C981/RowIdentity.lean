import Compact.Assembly.RowIdentity

namespace S12Completion.C981

/-- All twelve marker masks in the original retained case 981. -/
def family : Finset Nat :=
  {1, 2, 12, 48, 192, 512, 1024, 2048, 4096, 8192, 16384, 32768}

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 512).originalId = 981 ∧
    (N12Compact.RowIdentity.rowAt 512).groups = family := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_family :
    ∀ r ∈ S12.retainedRows, r.originalId = 981 → r.groups = family := by
  exact N12Compact.RowIdentity.family_at 512 981 family lookup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem family_retained :
    ∃ r ∈ S12.retainedRows, r.originalId = 981 ∧ r.groups = family := by
  refine ⟨N12Compact.RowIdentity.rowAt 512, ?_, lookup.1, lookup.2⟩
  apply List.mem_filter.mpr
  refine ⟨N12Compact.RowIdentity.rowAt_mem 512, decide_eq_true ?_⟩
  rw [lookup.1]
  decide +kernel

/-- This equivalence retains the universal packing and retained-row contract. -/
theorem excludes_case_iff :
    ExcludesCase 981 ↔ ExcludesFamily family := by
  constructor
  · intro h
    obtain ⟨r, hr, hid, hf⟩ := family_retained
    simpa only [hf] using h r hr hid
  · intro h r hr hid
    simpa only [row_family r hr hid] using h

end S12Completion.C981
