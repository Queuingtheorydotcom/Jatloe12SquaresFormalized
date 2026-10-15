import Compact.Bridge.C1092WallSymmetry
import Compact.Completion.C1092.OppositePair
import Compact.Completion.C1092.MMMM
import Compact.Completion.C1092.MMMP.TwoFifthsEntrance
import Compact.Completion.C1092.MPPM
import Compact.Assembly.RowIdentity

/-! The original retained C1092 obligation, with all four actual whole-packing
branches supplied. The historical conditional interface is preserved with
closed defaults. All new source still awaits compiler acceptance. -/
namespace N12Compact.C1092Compact
open S12 S12Completion
set_option Elab.async false

structure Pending : Prop where
  windmill : C1092WallSymmetry.BranchEnding 0 := C1092MPPM.windmill
  oneExceptional : C1092WallSymmetry.BranchEnding 1 :=
    C1092MMMPTwoFifthsEntrance.branch_ending
  adjacentPair : C1092WallSymmetry.BranchEnding 2 := C1092MMMM.adjacentPair

theorem all_branches (work : Pending) : C1092WallSymmetry.FourBranchEndings :=
  ⟨work.windmill,work.oneExceptional,work.adjacentPair,C1092OppositePair.oppositePair⟩

/-- Every original branch now has a source proof without a new hypothesis. -/
def pending_closed : Pending := {}

private theorem row_checked :
    (RowIdentity.rowAt 576).originalId = 1092 ∧
    (RowIdentity.rowAt 576).groups = C1092WallCycle.family := by decide +kernel

theorem excludes_case (work : Pending) : ExcludesCase 1092 := by
  intro r hr hid p hf
  exact C1092WallSymmetry.excludes_original (all_branches work) p
    (hf.trans (RowIdentity.family_at 576 1092 C1092WallCycle.family row_checked r hr hid))

theorem excludes_case_complete : ExcludesCase 1092 := excludes_case pending_closed

#print axioms excludes_case
#print axioms excludes_case_complete
end N12Compact.C1092Compact
