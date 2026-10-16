import Completion.Cases.C981.VectorData

/-!
Original-model C981 completion boundary. This imports the literal ownership
catalogue and `ExcludesVector`, not the large generated `Remaining` module.
The 62 previously connected representatives are still explicit proof inputs:
their old source was never Lean-checked. The other 55 are partitioned by the
action families in the archived plans. Those plan shapes are scheduling data,
not certificates and not assertions that each proposed trace is sound.

All inputs are statements about the original normalized packing. Supplying
every field, including complete catalogue coverage, suffices to exclude the
original case 981. Historical coverage is not assumed from an archive receipt.
-/

namespace N12Compact.Case981

def remainingIndices : List Nat :=
  [0,1,2,3,4,7,8,19,20,21,24,26,28,29,30,34,37,39,41,43,44,45,46,47,
   49,50,51,52,53,56,59,67,68,69,71,72,73,75,76,77,78,79,93,96,103,104,
   105,107,108,109,111,112,113,114,115]

def flatPairWall : List Nat :=
  [44,45,46,47,49,52,56,67,68,72,73,75,76,77,78,79,93,96,109,111,112,113,114,115]

def terminalStrip : List Nat := [108]
def stripBorder : List Nat := [7]
def kernelWithoutRefinement : List Nat := [8,69]
def angleRefinement : List Nat :=
  [0,1,2,3,4,19,20,21,24,26,28,29,30,34,37,39,41,43,53,59,71,103,104,105,107]
def centerSplit : List Nat := [50,51]

theorem remaining_count : remainingIndices.length = 55 := by decide

theorem routes_cover (i : Fin 117) (hi : i.val ∈ remainingIndices) :
    i.val ∈ flatPairWall ∨ i.val ∈ terminalStrip ∨ i.val ∈ stripBorder ∨
      i.val ∈ kernelWithoutRefinement ∨ i.val ∈ angleRefinement ∨
      i.val ∈ centerSplit := by
  have checked : ∀ j : Fin 117, j.val ∈ remainingIndices →
      j.val ∈ flatPairWall ∨ j.val ∈ terminalStrip ∨ j.val ∈ stripBorder ∨
        j.val ∈ kernelWithoutRefinement ∨ j.val ∈ angleRefinement ∨
        j.val ∈ centerSplit := by decide
  exact checked i hi

/-- The original case obligation, including every legal orientation and tie. -/
def RepresentativeExcluded (i : Fin 117) : Prop :=
  S12Completion.C981.ExcludesVector
    (S12Completion.C981.representativeVectors[i.val]!)

/-- Every actual packing realizing case 981 supplies an actual packing in a
listed representative. A diagonal reflection is allowed by choosing that
reflected packing as `q`. This still needs the full original ownership-domain
and symmetry proof; a finite check of the list cannot establish it. -/
def CatalogueCoverage : Prop :=
  ∀ p : S12.NormalizedPacking,
    S12.codedMarkerFamily p = S12Completion.C981.family →
    ∃ q : S12.NormalizedPacking,
      S12.codedMarkerFamily q = S12Completion.C981.family ∧
      ∃ i : Fin 117, S12Completion.C981.ownershipVector q =
        S12Completion.C981.representativeVectors[i.val]!

/-- No field is discharged by a source count or a numerical empty domain.
For V108 the three actual incoming covers (owners 5,7,11) must be proved;
for every border route the signed-angle/center/follower premises must be
derived from the same actual packing; every center split must cover both
closed children. These are restrictions on how the fields may be obtained,
not additional hypotheses of the original target theorem.
-/
structure Obligations where
  coverage : CatalogueCoverage
  formerlyConnected : ∀ i : Fin 117, i.val ∉ remainingIndices → RepresentativeExcluded i
  flat : ∀ i : Fin 117, i.val ∈ flatPairWall → RepresentativeExcluded i
  strip : ∀ i : Fin 117, i.val ∈ terminalStrip → RepresentativeExcluded i
  border : ∀ i : Fin 117, i.val ∈ stripBorder → RepresentativeExcluded i
  kernel : ∀ i : Fin 117, i.val ∈ kernelWithoutRefinement → RepresentativeExcluded i
  refined : ∀ i : Fin 117, i.val ∈ angleRefinement → RepresentativeExcluded i
  split : ∀ i : Fin 117, i.val ∈ centerSplit → RepresentativeExcluded i

theorem Obligations.all (proofs : Obligations) (i : Fin 117) : RepresentativeExcluded i := by
  by_cases hi : i.val ∈ remainingIndices
  · rcases routes_cover i hi with h | h | h | h | h | h
    · exact proofs.flat i h
    · exact proofs.strip i h
    · exact proofs.border i h
    · exact proofs.kernel i h
    · exact proofs.refined i h
    · exact proofs.split i h
  · exact proofs.formerlyConnected i hi

/-- This checks only the small literal indexing identity, not any geometry. -/
theorem catalogue_indexed : S12Completion.C981.representativeVectors =
    List.ofFn (fun i : Fin 117 => S12Completion.C981.representativeVectors[i.val]!) := by
  decide

/-- Completion of every explicit slot closes the original whole-case target. -/
theorem excluded_of_obligations (proofs : Obligations) : S12Completion.ExcludesCase 981 := by
  apply S12Completion.C981.excludes_case_iff.mpr
  intro p hf
  obtain ⟨q, hq, i, hi⟩ := proofs.coverage p hf
  exact proofs.all i q hq hi

end N12Compact.Case981
