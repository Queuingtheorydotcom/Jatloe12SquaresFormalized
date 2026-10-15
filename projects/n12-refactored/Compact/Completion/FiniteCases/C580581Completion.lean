import Compact.Completion.FiniteCases.C580581TripleEntrance
import Compact.Completion.OtherCases.C983.NegativeTripleEnd
import Compact.Assembly.RowIdentity

/-! Whole original C580/C581 source composition. The common entrance
retains the actual southeast owner 512, northeast owner 1024 and right
owner 16384, including their genuine pairwise disjointness. Its variant
parameter keeps bottom owner 8192 for C580 and 8196 for C581.

The only new finite checks identify the two unchanged retained rows.
`RowIdentity.family_at` covers every retained row of each original ID;
its inherited classification trust is unchanged. These source terms have
not been compiled or replayed and do not assert a global packing theorem. -/
namespace N12Compact.FiniteCases.C580581Completion
open S12 S12Pilot S12Completion C580581Entrance
set_option Elab.async false

/-- An arbitrary normalized packing in either complete original family
enters the shared three-square contradiction without an extra premise. -/
theorem family_impossible (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) : False := by
  obtain ⟨E,N,R,input,apartEN,_,_,_⟩ := C580581TripleEntrance.entrance v p hf
  exact Completion.OtherCases.C983.NegativeTripleEnd.impossible E N R input apartEN

private theorem row580 :
    (RowIdentity.rowAt 321).originalId=580 ∧
    (RowIdentity.rowAt 321).groups=family 0 := by decide +kernel

private theorem row581 :
    (RowIdentity.rowAt 322).originalId=581 ∧
    (RowIdentity.rowAt 322).groups=family 1 := by decide +kernel

theorem excludes580 : ExcludesCase 580 := by
  intro r hr hid p hf
  exact family_impossible 0 p
    (hf.trans (RowIdentity.family_at 321 580 (family 0) row580 r hr hid))

theorem excludes581 : ExcludesCase 581 := by
  intro r hr hid p hf
  exact family_impossible 1 p
    (hf.trans (RowIdentity.family_at 322 581 (family 1) row581 r hr hid))

#print axioms family_impossible
#print axioms excludes580
#print axioms excludes581
end N12Compact.FiniteCases.C580581Completion
