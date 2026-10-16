# Source-only delivery plan

Prepared 11 October 2026. No export, sync, compiler or numerical job was run
while preparing this plan. The existing delivery has not been changed.

## Selected source and hard budget

The latest complete virtual checkpoint is **294,934 Lean lines, 3,988 project
modules plus two drafts, 21,569,839 source bytes and 5,518,606 lexical items**.
The corresponding dependency audit counts **6,450 total modules: 3,988 project
and 2,462 external**. This is authenticated assembled-source planning, not
acceptance of the proposed proof instances or a bound on the unfinished global
proof. Any later source or manifest edit requires a fresh census.

`evidence/virtual-preferred-source-config.json` selects exact proposal overlays
over `evidence/preferred-delivery-roots.json`. It preserves all independent
mathematical roots and unresolved drafts. The complete six-case assembly
replaces the earlier fan-only root and C713 intermediate-relaxation root with
their actual source-to-target consumers. The two additional production roots,
`Compact.HistoricalCommon.All` and `Compact.HistoricalDirectPruning`, are counted
even though the principal theorem roots do not import them. Activation makes
such retained production modules explicit roots so export cannot omit them.

`scripts/export_delivery.py` uses the existing `verify.py` import resolver.
It refuses to write if **every delivered `.lean` file together** exceeds
300,000 lines or 40,000,000 source bytes. This includes the unresolved adapter
and the Lean cache-plan helper. It counts lexical items as a separate defense
against hiding large terms on long lines. It does not reduce the selected
roots to force a passing count. A failing cap requires a real source reduction.

`DirectPruningPlan` passed in 7.715 seconds and proves a genuine original
source-to-target transition without retaining intermediate pose tables.
Concrete candidate stages, whole entrances and chord stages are included in
the full virtual count; full ordinary replay remains required. The C898
replacement preserves its `CompleteCached` root and original case statement.
Older 298,422- and 306,487-line censuses describe narrower or earlier selections
and are not the current delivery count.

`RawSupportFanBool` is genuinely imported by the common-point support cache.
Its generic source stays in the closure; only standalone slower Bool benchmark
instances are superseded. The existing `DirectInitial.Inputs` and exact
fallback support helpers likewise cannot be removed by directory-name rules.

## Portable layout and provenance

Lean sources and executable scripts are exported byte-for-byte. Personal
absolute paths in those files cause a failure rather than an automatic edit.
Only documentation and metadata have local personal path prefixes redacted.
The export includes `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`,
the replay/resource/source-census scripts and the pinned dependency bootstrap.
It does not copy `.lake`, `.verification`, compiled objects, duplicate vendor
sources, large archived records, unactivated proposals or diagnostic modules.

The relative `.lake/packages` configuration depends on the documented explicit
bootstrap step. Mathlib is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; the bootstrap's other source revisions
come from that Mathlib manifest. The export checks local `.source-pin` records
against these revisions and emits `evidence/dependency-pins.json`. No dependency
or toolchain download is automatic. Source pins are not a hash audit of every
external compiled object, and those object caches are not shipped.

The imported original-model overlay is preserved in the actual closure.
`imported-source.json`, scalar SAT provenance, the seven-source inventory and
the mathematical audit notes retain attribution and reconstruction evidence
without embedding the old enormous generated proof. Archive-local references
inside those notes describe historical evidence, not hidden build inputs.
The explicit small-evidence allowlist also preserves the all-six common-point
manifest/stage scope, support selections and empty certificates; C898's exact
audit and production-proposal manifests; the current source/import census;
the latest branch heads with detailed comparison/tree review; and C977/C981
archive/member provenance. Whole-archive hashes and hashes of individual ZIP
members remain separately identified. The fresh delivery census supersedes
older scoped counts; the included older census retains its original root list.
Large archived JSON/Lean records and duplicate dated whole maps stay local.
Jatloe's original model attribution and Muhammad Maaz's SOS article credit
remain in the README; the article is credited as a suggested discovery method,
not as a tactic/certificate used here.

## Acceptance reconciliation

The export recomputes exactly the local configuration/source/dependency
fingerprint formula in `scripts/verify.py`, verifies saved object hashes, and
requires every local dependency to have a current matching receipt before
labeling a module `current_local_acceptance`. Changed source or dependency
hashes, missing objects, and missing receipts stay explicitly distinct from
current acceptance. Saved acceptance time is historical, not a new replay time.

`delivery-acceptance.json` contains sanitized statuses, exact hashes and only
matching-log axiom lines. It never ships opaque compiled objects as proof
sources, never changes `Pending` into a proof, and never claims the global
theorem. Source status can still be conditional even when the module checks.
The inherited original `Lean.ofReduceBool` dependency remains visible wherever
the actual matching axiom log reports it. Logs whose hashes no longer match
are not used for an axiom claim.

Export does not require every source module to be accepted. It emits a prominent
`VERIFICATION-STATUS.md` with the exact matching receipt count, unverified build
module count and unresolved draft count. A source checkpoint assembled without
pilot gates is explicitly labeled. Source export never synthesizes a success
receipt or converts an unverified candidate into a checked theorem.

`delivery-source-budget.json` records every delivered Lean file and exact
SHA256. `delivery-files.json` hashes every other delivered file, with its own
self-exclusion explicit. This is enough to identify the source snapshot
independently of later edits or stale acceptance receipts.

## Safe installation, only after parent authorization

`scripts/activate_virtual_proposals.py` is a source transaction before export.
The default mode requires explicit accepted pilot gates. Its separate
`--assemble-unverified` mode permits assembling an authenticated source
checkpoint without those gates; it records no Lean acceptance and requires
fresh ordinary verification afterward. Both modes preserve all exact source,
manifest, import-closure and 300,000-line checks, source backups and rollback.
Neither mode changes `SymbolicRegistry`, `Remaining117`, acceptance receipts or
compiled objects. The three-GiB free-disk floor includes a reserve for new source
and backups. Explicit interrupted rollback is authenticated and resumable.

The export defaults to a read-only plan. A write requires `--write`; replacing
the existing selected project additionally requires `--replace-existing`.
It stages the complete bounded snapshot in a sibling directory, takes an
exclusive export lock, preserves the entire former delivery in a timestamped
sibling backup, then renames the completed stage into place. On installation
failure it restores the former directory and removes only its own staging
files. It does not touch Git, publish, delete the previous delivery or start
background work. Parent must account for that small preserved backup in total
disk usage and remove it only when no longer needed.

The root worker should run the ordinary bounded source plan after production
activation, inspect the exact full count and receipt-status summary, then
authorize installation into the selected project. A broad `lake build` is
not part of export: case imports must remain explicit because the unresolved
C696 adapter and named conditional obligations are intentionally still open.

## Remaining delivery caveats

* `adapters/C696SymmetryOriginal.lean` imports the absent original
  `Completion.Cases.C696.RootZeroSymmetry`. Preserve the useful draft and exact
  missing name; do not pretend it is an import-closed checked root.
* The C981 stronger corner-seed draft retains its original statement/proof
  verbatim and all present dependencies. Its two unavailable original helpers
  have exact hashes recorded. The catalogue route needs only the separately
  proved elementary ownership/splitting facts; the stronger theorem is not
  treated as an assumption of that route.
* `PairStep14CommonPoint` passed its whole original terminal replay in 10.396
  seconds and is now integrated into `CompleteCached`. Whole C898 still needs
  its complete remaining source replay.
* All 59 actual remaining original case contracts stay explicit. Neither
  registry acceptance nor a compact graph skeleton fills them.
* No present count bounds the missing mathematical certificates below one
  million lines. The final source/import/cache/disk counts are separate gates.
* The 6,450-module external/import checkpoint uses the complete virtual
  selection; it must be refreshed if final roots or overlays change.
