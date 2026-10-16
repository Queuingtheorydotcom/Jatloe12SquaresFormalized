# Direct-cover boundary materialization

The first C898 direct-cover root passed. The second root, angle1 with original
target pose1122, overflowed during construction even when compiled alone.
Independent replay accepted its recipe, selected base forms, forbidden forms
and target rows. Only materializing `PlanarBoundaryAuto.activeRows` overflowed.
Thus neither the eight-root batch nor the vertex numeric theorem caused this
failure. No resource or stack limit was raised to address it.

`Compact/Core/BoundaryHintSyntax.lean` replaces that reduction with an untrusted
local hint constructor. It reads the already materialized closed integer rows,
preserves the original last-occurrence boundary order, and scans at most64
base rows against at most128 total rows. For an excluded boundary it emits
one original base index and an integer scale/multiple. A boundary without a
recognized exclusion remains in the retained list. It does not run the
recursive automatic-search expression or create a proof of the search result.

`Compact/Core/PlanarBoundaryHints.lean` binds this data with two kernel proofs:

- The existing `PlanarBoundaryFilter.FilterCheck` certifies every discarded
  original boundary, including the strict negativity needed for exclusion.
- An exact equality binds the cached rows to the entire retained list from
  the checked plan. An omitted retained boundary therefore fails acceptance.

The ordinary triangle checker then checks every unordered retained pair.
`Cache.toCheck` invokes the existing filter soundness theorem to recover the
unchanged `PlanarVertexCheck.Check`. All original pose-input memberships,
forbidden open blocks, target strictness and angle coverage remain in the
existing original-model bridges.

There is no native proof evaluation, new axiom, unchecked shortcut or case
assumption. The constructor emits ordinary data and each chosen hint is
checked independently. Failed construction or checking stops compilation.

The focused replay root
`Compact.Cases.C898.RecipeInitial.Single01Hinted` passed, using the exact
second-root base, forbidden and target caches. The generic hint checker,
syntax and fully integrated second-root entry also passed the parent's
guarded replay with ordinary axioms.

The subsequent64-root owner module hit the newly lowered600MiB aggregate
physical-footprint guard at630,512KiB, with no Lean source error. The source
now places the same eight-entry numerical batches in separate modules,
then assembles their checked entries into the unchanged original owner.
The original64 Spec records and final owner0 assembly theorem bodies were
preserved. No new target pool, hint table or geometric case split was added.

The initial eight-root module still exceeded the guard while checking one
combined conjunction. The accepted `DirectRecipeCheck` now checks strictness
on exact cached integer targets and proves the unchanged `Entry.Check`.
It also explicitly restricts all finite decisions to their supplied lists.
The authentic single-entry literal check passed in1.591 seconds.

The final production layout keeps eight roots per module but names each entry
and proves each numerical fact in a separate theorem command. All eight
numerical facts in `Compact.Cases.C898.RecipeInitial.Batch00_00` passed in the
parent's13.854-second attempt without hitting the guard. That attempt found
only a missing empty-list tail in the final logical composition; the source
now supplies that tail explicitly. Final module acceptance is pending.

`scripts/prepare_c898_spec_initial.py --run` is prepared to emit this layout
for all704 original records, in88 eight-root modules. It does not create704
single-root modules and does not change the eleven original owner interfaces.
The reusable `CheckedRecipeCommand` subsequently passed in9.244 seconds and
its authentic eight-root `CommandPilot` passed in12.680 seconds, under the
same600MiB physical-footprint guard. Each source record expands to the same
named cache and ordinary `decide +kernel` theorem as the separate-command
layout. This removes repeated declaration scaffolding while retaining the
per-root numerical proof boundaries; it does not combine eight decisions.

The producer now emits that command for all704 roots and asserts exact equality
of every semantic record to its preceding proposal. It writes proposals only.
`scripts/activate_c898_spec_initial.py --run` is prepared for parent-controlled
activation: it checks original-input and proposed-source hashes, rejects changed
active files, and archives replaced source outside the active import closure.
The complete704-root and whole-owner replay remain outstanding.
