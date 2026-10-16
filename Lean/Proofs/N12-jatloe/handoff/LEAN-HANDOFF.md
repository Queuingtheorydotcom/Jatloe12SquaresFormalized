# Lean handoff: twelve-square compact refactor

Checkpoint: 11 October 2026. Repository: `EvolvingPrograms/SquaresLean`, branch
`12Refractored`, project directory `projects/n12-refactored`. The ZIP is also a
standalone project: use its top-level project directory as your working directory.
Read `CHECKPOINT.md` first and `MATHEMATICS-HANDOFF.md` for the unsolved geometry.

## What you are receiving

The original goal is `S12.packingConstant12 = 4`, for twelve congruent unit squares
with arbitrary orientations and disjoint interiors, allowing boundary contact.
The attaining construction and original normalization/classification are retained.
This is an **unfinished source checkpoint**, not a completed formal proof.

The preferred conditional assembly has 86 whole original-case source terms and
31 pending original-case contracts. Seventy-nine entries are in the symbolic
registry; seven are compact replacements for recovered historical proofs. The
new source, including C84, C696 and the complete C977 ending, awaits Lean replay.
The earlier 58-entry registry had a scoped replay; that historical success does
not certify changed source or changed transitive dependencies.

The exact preferred closure plus three explicitly retained drafts is 343,370
Lean lines, 4,352 project modules, 25,719,709 source bytes. This is above the
approximate 300k assembly target. Neither a final sub-million-line bound nor a
whole-proof compilation-time estimate is established. External Lean/Mathlib
dependencies are additional: the user's module cap is a compilation-time proxy,
not permission to omit their actual rebuilding cost.

The complete source snapshot also retains unselected current source files so
that partial mathematical work and alternate implementations are not lost.
`handoff/source-inventory.json` identifies preferred versus unselected files.
These are different scopes. Do not import every retained alternate at once.

## Exact completion boundary

Start with these files, in this order:

1. `Completion/Contracts.lean`: `S12Completion.ExcludesCase id` quantifies over
   every retained row carrying the original ID and every actual normalized
   packing with that row's marker family.
2. `Compact/Assembly/Remaining117.lean`: the genuine original 117-case route,
   proof-bearing `ProvenCase`, partition, and conditional original optimality.
3. `Compact/Assembly/SymbolicRegistry.lean`: 79 whole-case source entries and
   their exact 38-case complement before adding the historical seven.
4. `Compact/Assembly/SourceAssembly.lean`: adds 701, 713, 717, 898, 973, 978 and
   979; exposes 86 source entries and 31 pending original IDs.
5. `Compact/Assembly/ContinuousRemaining.lean`: the current continuation
   skeleton. Its `Pending` fields are the same remaining actual obligations,
   with C981 and C1092 expanded into their more useful interfaces.

The precise 31 pending IDs are:

```
48,573,574,580,581,683,700,702,705,715,716,867,868,888,889,893,
896,972,974,975,976,981,982,983,997,1072,1084,1089,1090,1091,1092
```

`Pending.other_cases` covers the 29 IDs other than 981 and 1092.
`Pending.case981` is `N12Compact.C981Compact.Pending`, which asks for the
42 unfinished **whole representative-vector** exclusions. Catalogue and actual
packing symmetry coverage are already consumed by `C981Compact.excludes_case`.
`Pending.case1092` is `C1092WallSymmetry.FourBranchEndings`, four complete
actual-packing sector contradictions. No field is filled by an admission.

An accepted theorem of the form `optimality (work : Pending)` is still
conditional. Completion requires actual terms for all fields and an
unconditional final theorem, followed by its complete replay and axiom report.
Do not substitute the older 18-slot `CaseSlots` route: its separate 117-to-18
reduction remains a conditional interface.

## Newly assembled whole cases and current partial work

| Obligation | Source endpoint / primary reading | Exact status |
| --- | --- | --- |
| C84 | `Compact/Assembly/C84.lean`; `audit/C84-SYMBOLIC-COMPLETION.md` | Whole original case, source complete; actual ownership budgets and a continuous two-square contradiction |
| C696 | registry binding; `audit/C696-GLOBAL-COUPLING.md` | Whole original case, source complete; a bottom-wall tilt contradiction replaces the historical transition fan |
| C977 | `Compact/Bridge/C977CenterClosure.lean`, `excludes` | Whole original case, source complete; all central/bottom signs, original missing-corner cover, independently reviewed |
| C981 | `Compact/Cases/C981Compact.lean` | 75 of 117 representative vectors supplied in source; 42 remain; original case remains open |
| C981 34/41 | `OuterTopElbow*.lean`; `audit/HANDOFF-C981-POSITIVE.md` and `HANDOFF-C981-NEGATIVE.md` | New exact reductions; neither whole vector closed |
| C1092 | `Compact/Cases/C1092Compact.lean`; `audit/HANDOFF-C1092.md` | Four genuine whole-packing sectors remain open |
| 48/573/574 | `Compact/Bridge/C48RightBarOwnership.lean` | Shared original-budget entrance; whole geometric ending remains open |
| C868 | `Compact/Cases/C868/`; `audit/C868-UPPER-STRIP.md` | Partial sectors only; whole case remains open |

For C977 read `audit/C977-COMPLETE-ENDGAME.md`, then the negative-bottom and
positive-bottom wall receipts. The center adapter canonicalizes each real square
while preserving its entire interior; it does not reflect the whole configuration
and silently change the missing-corner premise. Endpoint/zero-angle cases remain
part of the source proof. Mathematical reviews are evidence about the argument,
not Lean elaboration or successful tactic execution.

## Source layout and important alternate routes

- `source/S12/`: retained original foundation and intentionally compact replacements
  in the original namespaces. `source` is configured as S12's source directory.
- `Completion/`: original contracts and genuine C977/C981 ownership interfaces.
- `Compact/Geometry/`: continuous inequalities, full-square separating axes,
  support cycles, wall/corner bounds and other reusable mathematics.
- `Compact/Bridge/`: actual original-owner, marker, orientation and symmetry adapters.
- `Compact/Assembly/`: exact original-case contracts, registry and final skeleton.
- `Compact/Preservation/Complete/`: assembled six-case compact replacements.
- `Compact/Cases/C898/CompleteCached.lean`: preferred seventh recovered case.
  `C898.Complete` is a legacy alternate; importing both can duplicate declarations.
- `Compact/HistoricalCommon/`, selected `HistoricalData/`, and case data: compact
  finite witnesses and their ordinary soundness/assembly, not trusted external oracles.
- `adapters/`: three deliberately retained drafts with named missing original
  imports; they are not accepted build roots. See the preferred manifest.
- `audit/`: mathematical explanations and dated evidence. Older narratives are
  historical; the current checkpoint and executable source boundary take precedence.
- `scripts/`: source-only inventory/packaging tools, bounded runner and eventual
  verifier; also historical recovery/proposal producers, which need separate inputs.

Superseded generated payloads, duplicate vendor source, original private ZIPs,
dependency caches, compiler objects, account data and local conversation logs are
not shipped. A source-only inventory records the omitted evidence inputs. The
current preferred import closure is self-contained in project source, except for
the external pinned libraries and explicitly named retained drafts. There is no
dependency on running a recovery producer to elaborate the preferred sources.

## Toolchain and environment

- Lean: `leanprover/lean4:v4.19.0` (`lean-toolchain`).
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Additional package pins: `handoff/dependency-pins.json`.
- Local Lake configuration: `lakefile.toml`, package name `n12_compact`.
- `scripts/verify.py` locates the usual Elan 4.19.0 installation under the current
  user's home directory. If the receiving system uses another installation path,
  change that tool path only; preserve the version and mathematical source.

The parent repository also contains an older N11 project with a different build
configuration. Always work inside `projects/n12-refactored`; do not run the root
repository's build/CI and mistake it for checking n=12. Its existing workflow is
manual dispatch only and does not verify this new project.

No toolchains or dependency caches are included. Restore dependencies only when
needed and within a measured disk budget. `scripts/bootstrap_sources.py` restores
the pinned public sources, not compiled caches. `prepare_cache.py` and
`restore_cache.py` involve Lean cache helpers/network access; do not run them as
part of a source-only handoff inspection. They are eventual setup tools, not
proof verification. Historical producers use optional `N12_LEGACY_PROJECT`,
`N12_LEGACY_CHECKOUT`, `N12_EARLIER_ZIP`, or explicit input arguments; none is a
prerequisite for the current preferred source closure.

## Work order: write first, compile the whole proof at the end

The user explicitly deferred compilation until the complete proof source is
assembled. This checkpoint was packaged without running Lean or Lake. Preserve
that instruction while completing the missing mathematics and source.

1. Read the exact pending contract; assign whole cases or disjoint full-vector/
   sector obligations. Keep a single owner for registry changes.
2. Derive a continuous mathematical argument and verify every premise against
   the original packing. Prefer shared support identities to pose/angle grids.
   If a case split exceeds 100 cases, simplify the argument before expanding it.
3. Write generic mathematics, then the actual-owner adapter. Review all signs,
   every separating axis/direction, strictness, split boundaries and square-side
   equality. Register only whole original contracts.
4. Update exact pending IDs and source inventories after integrating an entire
   obligation. A forced point, one angle sector or one sign case is partial.
5. Once all fields have terms, write the unconditional original theorem and
   `#print axioms` for it. Then run the complete project closure serially under
   the guard, fix failures without weakening statements, and repeat affected
   dependencies until the full proof passes.

Read-only closure inspection is available now, without Lean:

```sh
python3 scripts/verify.py --plan Compact.Assembly.ContinuousRemaining
```

The eventual replay runner is `scripts/verify.py`, wrapped in `scripts/bounded.py`.
For example, **only once the complete source is ready**, substitute the actual
unconditional final module into:

```sh
python3 scripts/bounded.py --rss-mib 1800 --footprint-mib 600 \
  --free-gib 3 --seconds 600 --receipt .verification/final-resources.json -- \
  python3 scripts/verify.py Compact.Assembly.Final
```

`Compact.Assembly.Final` does not exist yet; the example intentionally does not
claim a finished target. A 600-second guard is a safe initial time budget, not a
forecast of full replay. Extend time deliberately on an adequate machine while
keeping memory/disk bounds and one compiler process group. The runner checkpoints
matching source/dependency/object receipts, so interrupted serial progress can be
resumed without trusting stale objects. Add all retained preferred roots to the
eventual source-preservation replay as well; the unconditional theorem's closure
is the acceptance boundary for the actual theorem.

The default `Compact` library root checks reusable material and is not the global
theorem. The runner's `SCOPED_REPLAY_PASS_GLOBAL_OBLIGATIONS_OPEN` output is
deliberately not a global-success marker. A successful conditional assembly still
requires inspection of the final theorem's type and remaining inputs.

## Trust and resource requirements

No new `sorry`, `admit`, custom axioms, unsafe oracles, or new native decision
sites. Ordinary Lean proofs must justify geometry, checker soundness, original
entrances, exhaustiveness and assembly. The inherited original numerical
foundation contains `native_decide`; its `Lean.ofReduceBool` dependency must be
reported in the final axiom audit. Do not call this a compiler-independent kernel
proof merely because the new geometry uses ordinary tactics.

Use the bounded runner for any material local job. Keep aggregate project storage
below 10 GB, check free disk independently, and keep concurrent computational
jobs at one. Reasoning workers may be parallel, with explicit file ownership.
The guard terminates and reaps its process group on failure. Do not defeat the
resource policy with unguarded child processes or compressed-memory growth.
The pinned Lean rejects the previously tried internal `-M` option; use the
external guard. No large case-table generation is the default continuation.

## Acceptance deliverable for the next Lean agent

Return the changed source, an exact list of newly discharged whole obligations,
remaining mathematical gaps, and a current closure/size report. When the complete
proof is finally assembled, additionally return the source revision, full replay
receipt, final unconditional theorem signature, and actual axiom report. Local
helper tests, hand reviews, historical PASS receipts and numerical certificates
alone do not establish the unrestricted global theorem.

Credit Jatloe for the original n=12 sources. Muhammad Maaz's SOS tactic article,
https://mmaaz.ca/writings/sostactic.html, was suggested by the user as a possible
discovery method; no SOS tactic/certificate from it has been used in this refactor.
