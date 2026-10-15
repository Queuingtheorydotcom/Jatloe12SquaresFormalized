import Compact.Bridge.C1092WallSymmetry.ContextTransport
import Compact.Bridge.C1092WallSymmetry.BranchClassification

/-! Four genuine D4 wall-sign sectors of the original C1092 family.
The factored dependencies preserve all original public declarations.
Whole-packing transport retains actual owners, closed cuts and strict points. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

/-- Every original C1092 packing enters one of four canonical sectors as
one complete transformed packing, retaining its actual twelve squares. -/
theorem original_four_branches (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ u : Fin 8, ∃ k : Fin 4,
      codedMarkerFamily ((symmetry u).pullPacking p) = family ∧
      WallContext ((symmetry u).pullPacking p) (canonicalBranch k) := by
  obtain ⟨b,hb⟩ := original_wall_context p hf
  obtain ⟨u,k,he⟩ := branch_coverage b
  exact ⟨u,k,family_transport _ p hf,he ▸ context_transport _ p hf b hb⟩

def BranchEnding (k : Fin 4) : Prop :=
  ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    WallContext p (canonicalBranch k) → False

/-- Four remaining whole-packing obligations. They are hypotheses, not
axioms or claims that any original branch has already been excluded. -/
structure FourBranchEndings : Prop where
  windmill : BranchEnding 0
  oneExceptional : BranchEnding 1
  adjacentPair : BranchEnding 2
  oppositePair : BranchEnding 3

theorem excludes_original (finish : FourBranchEndings) :
    ∀ p : NormalizedPacking, codedMarkerFamily p = family → False := by
  intro p hf
  obtain ⟨u,k,hfamily,hcontext⟩ := original_four_branches p hf
  fin_cases k
  · exact finish.windmill _ hfamily hcontext
  · exact finish.oneExceptional _ hfamily hcontext
  · exact finish.adjacentPair _ hfamily hcontext
  · exact finish.oppositePair _ hfamily hcontext

#print axioms original_four_branches
#print axioms excludes_original

end N12Compact.C1092WallSymmetry
