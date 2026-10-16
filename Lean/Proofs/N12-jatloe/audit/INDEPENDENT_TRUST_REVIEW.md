# Independent source review and portable subset

Snapshot: 2026-10-11 01:13:58 UTC. This is a source/interface review, not a new
Lean replay. The root worker was still repairing and checking the assembled
project. Source hashes, exact paths and explicit import closures are recorded
in `portable-source-inventory.json` beside this report.

## The original theorem is preserved

`Compact/Assembly/Frontier.lean` concludes the original
`S12.packingConstant12 = 4`. Its reduction quantifies over every original
`NormalizedPacking`, produces an allowed transformation and an actual retained
row, and proves that row belongs to the 18-case frontier. The final theorem
still requires that reduction and exclusions of every frontier case. No
inhabitant of this obligations structure has been supplied.

`Compact/Assembly/CaseSlots.lean` spells out all seven historical and eleven
remaining complete `ExcludesCase` inputs. Its literal 18-way split neither
weakens those predicates nor discharges them with saved leaves. Supplying the
18 cases without the global reduction would still be insufficient.

`Compact/Cases/C981.lean` now imports only the lightweight original vector
data and exposes catalogue coverage as a separate mandatory field. Its
coverage statement says every packing of the original family yields some
packing of that family with one of the 117 representative vectors. It does
not demand that the witness is the original packing or its reflection, but
this is logically sufficient: excluding every such witness contradicts the
existence promised by coverage. The statement is an outstanding geometric
obligation, not a consequence of checking the list length. The remaining
fields cover all 62 previously connected vectors and all 55 remaining
representatives. No such fields are silently assumed to be inhabited.

`Compact/Cases/C981V116.lean` transports the new midpoint contradiction to
the exact original ownership vector 116. It obtains all point membership,
nonmembership, side and disjointness facts from the original packing model.
It is a whole-vector source proof, not a whole C981 exclusion. Vector 116 was
already among the historical 62 source-connected representatives, so this
replacement does **not** reduce the 55 previously missing representatives.

## New geometric interfaces

- The midpoint proof uses arbitrary original square orientations and derives
  a positive frame by reindexing faces. It handles the equal-component split
  and uses actual strict interior membership and disjointness.
- The congruent SAT bridge derives the four weak separating alternatives
  from actual disjointness. Equal side lengths are already part of normalized
  packing. It adds no separation oracle or excluded contact assumption.
- The long-section theorem covers every orientation, including zero frame
  components and equality at the permitted radius. Strictness comes from the
  original side being greater than one. The capacity theorem is conditional
  on proving that each actual square has one of those sections.
- The C977 chain theorem still requires the stated near-axis, height,
  ordering and gap bounds. Its geometric disjointness input is real, but
  obtaining those case-entry bounds remains work.
- The three-square radius theorem derives the long sections and SAT facts
  rather than assuming them. Its remaining inputs include the original
  side cap, near-horizontal bounds, center intervals, the closed anchor
  point, container bounds and radius inequalities. It does not itself prove
  that every unresolved case enters that interface.
- The C696 symmetry result is an abstract transfer theorem for a supplied
  packing automorphism. Four-square anchors require their three closed
  containment premises. Neither result supplies missing case coverage.
- The generic DAG and linear-certificate theorems are soundness interfaces
  with explicit local-step/check premises. They are not instantiated
  complete exclusions of the unresolved cases.

No weakened final theorem, hidden discharged coverage, admission, new axiom,
unsafe declaration or foreign implementation annotation was found in this
active source closure. This statement concerns the reviewed source and
declaration types; kernel acceptance remains separately recorded.

## Native trust and replay boundary

The active original foundation contains **723 `native_decide` sites**:
CoreData 419, CoverData 24, DomainSpecData 128, FourPointData 111,
LocalQueryData 35, Raw 3 and To117 3. The newly introduced compact source
has no native decision site. Consequently a checked new geometric theorem
may use only the ordinary axioms while the complete original-model assembly
still inherits `Lean.ofReduceBool` through its foundational facts.

At this snapshot, 38 active source files have matching successful source-hash
receipts. This is weaker than checking their complete dependency fingerprints.
The saved `Compact` root receipt refers to an older source hash, and no
receipts yet exist for CaseSlots, C981 or C981V116. Do not describe the current
four roots as replayed merely because their individual geometric ingredients
have been checked. A comment in `Compact/Bridge/BorderEndpoint.lean` still
calls it uncompiled; this is stale if its current fingerprint is accepted,
and is not evidence of a fresh failure.

## Exact portable source subset

The union of these roots and all 16 small C977 modules has **118 project
modules, 1,390,707 source bytes, and 15,075 newline-counted source lines**,
with no missing project import:

- `Compact`
- `Compact.Assembly.CaseSlots`
- `Compact.Cases.C981`
- `Compact.Cases.C981V116`
- Every module under `Completion/Cases/C977`

Use exactly `source_inventory.files` in `portable-source-inventory.json` as
the source manifest. The smaller union using only C977.AuxiliaryContext has
116 modules, 1,381,495 bytes and 14,864 lines; it omits the standalone
PoseEnclosure and BorderPoints helpers. The complete C977 reduction remains
conditional on contradictions for the covered contexts; its 912-context
coverage theorem is not an exclusion.

Also include the pinned toolchain, Mathlib revision/manifest, the verification
entrypoint, source hashes and relevant provenance/license notices. The current
Lake configuration points Mathlib at `.lake/packages/mathlib`. Copying only
the project files therefore does not by itself create a portable build:
provide a pinned dependency bootstrap or use a pinned Git dependency.
Existing `.lake` objects and Mathlib/Lean caches are not project source.
The default Lake target is only `Compact`; the other roots must be explicit
verification targets if they are part of the advertised package.

The inventory separately lists 72 inactive modules and their missing imports.
Keep the historical `To18`–`To116` chains, `CurrentReduction`, the listed
`BatchedPush` wrappers, and `SharedCase1089` as provenance, not active build
targets: their generated proof imports are absent. The original C981
CaseVectors/Geometry/DiagonalAuxiliary/OwnershipDomains/DomainReuse/
CornerReduction modules and Case976Domains currently wait on three small
original helpers; an in-progress bounded archive recovery may resolve those
missing imports. Their old status must then be refreshed, rather than
treated as permanently missing. Recovered Compact text decoders are also
provenance until their original transitive checker dependencies are present.
Diagnostic ClassificationPrefix modules, MarkerImportProbe and the unused
C696 fixture are not needed by this portable union.

These counts measure the currently assembled reusable rules and conditional
interfaces. They are not a demonstrated compression of the seven accepted
historical exclusions, the 117-to-18 reduction, or the whole theorem. The
README correctly marks global optimality unfinished and says the final
sub-million-line requirement is not yet established. No stronger global
size or completion claim is warranted by this small source footprint.
