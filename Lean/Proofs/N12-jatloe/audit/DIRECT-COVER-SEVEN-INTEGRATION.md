# Direct initial cover integration for the seven historical cases

This is a source and interface audit. It does not claim that the seven compact
case exclusions have passed Lean. The finite audits and focused replay receipts
have different scopes.

## Exact initial obligations

The six-case `evidence/historical-direct-cover-audit.json` reports no failed
root and no unsupported owner slot. Together with the separate C898 audit:

| Case | Original owner slots needed | Angle obligations | Empty intervals |
|---|---:|---:|---:|
| 701 | 12 | 768 | 26 |
| 713 | 9 | 1,152 | 94 |
| 717 | 11 | 1,408 | 58 |
| 898 | 11 | 704 | 74 |
| 973 | 11 | 704 | 5 |
| 978 | 9 | 576 | 10 |
| 979 | 12 | 1,536 | 45 |
| Total | 75 | 6,848 | 312 |

Thus the required initial replacement has 6,536 surviving reduced poses and
312 genuine empty-angle obligations. Empty roots must remain in each owner's
angle-cover list: dropping them would remove the proof that every actual
orientation is handled. Their target is the impossible inequality -1 >= 0.

The exact original slot lists matter. For example, case713 needs slots
0,1,5,6,7,8,9,10,11; case717 omits slot5. No twelve-slot template may silently
invent or omit an original entrance premise. The audited side bounds remain
1 < side <= 1001/1000 in the original side-four container.

## Accepted C898 boundary and current recipe preservation

The parent reports acceptance of C898 Data00 (63 additional root checks and
assembly,132.501 seconds) and its original-domain Owner00 bridge (24.513
seconds). The first pilot root was accepted separately. This supplies one
complete original owner enclosure, not the other ten or the whole case.

The prepared `scripts/build_c898_recipe_initial.py` preserves the same data:

- It authenticates exactly the inputs used by the complete704-root audit.
- For each owner it matches the complete ordered target pose-ID list against
  `evidence/c898-domain-map.json`.
- It preserves each target's original row ID order, including repetitions.
- Its target pools deduplicate only storage; recipes map the same original
  row IDs to local indices and reconstruct the exact original sequence.
- Eight-root batches are concatenated in increasing angle order. All64 angle
  intervals, including the74 empty intervals across owners, remain present.
- Input selection stores original constraint indices. All forbidden blocks
  are derived from the full original outside-point list with strict bits and
  four-face order preserved.
- Kernel equality of the resulting complete leaves to the original reduced
  domain is a separate required theorem. Pool defaults cannot weaken this
  equality obligation.

The recipe variant has not been counted as accepted. It is emitted to a
separate namespace, leaving the accepted DirectInitial owner intact.

## Shared owner entrance

`Compact/Bridge/DirectOwnerFamily.lean` supplies one reusable original-packing
entrance proof for all75 owner records. A `CertifiedOwner` bundles:

1. The original independently proved auxiliary ownership domain.
2. The direct owner enclosure and its complete continuous-angle check.
3. The checked original point-premise link, including any certified common
   points used by the historical entrance.
4. The exact original reduced pose list and equality of the enclosure's
   leaves to that list.

`CertifiedOwner.sound` derives oriented coverage of the actual packing square
at `ownerIndex p domain.mask`; it does not assume the packing's point ownership
or pose coverage. `certified_owners_sound` assembles any finite list of these
records. This interface is independent of the angle grid, so the128-interval
owners need no separate semantic proof template.

The generic module is source-complete and awaits the parent's replay. Once
accepted, each case's entry emitter should instantiate the75 records and use
the shared theorem. It should retain existing final `ownerN_cover` signatures
to avoid modifying propagation semantics.

## Form sharing and replay cost

The updated prepared recipe checker caches each root's encoded geometric
forms. `DirectCachedRecipe` stores the exact materialized base and forbidden
forms plus the active rows produced by `PlanarBoundaryAuto.activeRows`.
Three ordinary-kernel equality proofs bind these caches to their original
definitions. Eight-root batches then check only cached integer constructors.
The generic discovery theorem replaces all serialized boundary-hint files.

Focused pilot receipts reported by the parent accepted CachedPilot in4.380
seconds, CachedUnorderedPilot in2.169 seconds, and CachedFilteredPilot in1.803
seconds, all with ordinary axioms. These are individual module timings, not
a demonstrated timing for the updated complete704-root recipe route. Its
emitter and generic assembly still await their own replay.

Target storage is shared per owner. Encoded geometric forms are currently
cached per root; they are **not** shared across different owners or cases.

For further sharing across owners, the reusable cache key should be:

- the complete rational angle-enclosure value, not its case-local angle index;
- outer point, inner point, or wall formula kind;
- the exact rational point coordinates and strictness/form order.

The same point/angle formula may then be encoded once across owners and cases.
The actual root should still materialize or select a small local row pool for
its integer loop, rather than repeatedly indexing a huge global dictionary.
An exact equality to the original base/forbidden lists must be checked once
per root. This shares actual computation and data; it does not merely shorten
printed coefficient lists. A bounded count of distinct keys is still needed
before assigning a numerical savings factor.

## Remaining whole-case obligations

Initial coverage alone does not finish any of the seven cases. The current
postforest inventory still reports642,781 pair declarations,33,366 remaining
pose declarations,13,057 distinct pair contexts, and17,946 unresolved pair
bindings. Those are structural counts, not checked compressed certificates.
They exclude some adapter and non-pair costs explicitly listed in the report.

Finish the complete C898 chain first, then reuse only its accepted primitives
where each historical transition matches. Case entrance proofs, propagation
neighbors, relaxed target domains, chord transitions, and final empty-owner
contradictions must all remain exact. Neither a300,000-line preserved-work
bound nor a sub-million-line full formalization follows from the initial-cover
audits alone.
