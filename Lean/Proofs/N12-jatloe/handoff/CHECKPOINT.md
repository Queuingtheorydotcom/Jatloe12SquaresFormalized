# Publication checkpoint — 12Refractored

11 October 2026. Original repository: `EvolvingPrograms/SquaresLean`.
This project is published at `projects/n12-refactored` on branch `12Refractored`.
Its parent checkpoint is `c5c6144349a141e56ac43c81ed732f731c591eac`.
The two ZIPs record the exact new publication commit in their `PUBLICATION.json`.

**The full theorem is unfinished.** The exact original target is
`S12.packingConstant12 = 4`, with arbitrary orientations and allowed boundary
contact. The current assembly contains 86 whole original-case source terms,
leaving 31 original-case obligations. C981 has 42 unfinished representative
vectors; C1092 has four open whole-packing symmetry sectors. These are nested
obligations inside two of the 31 cases, not additional original case IDs.

The latest whole-case source additions are C84, C696 and C977. The final C977
original adapter has received two independent mathematical/source reviews.
**None of the newly changed source was compiled for this publication.** The
user requested compilation only once the complete proof source is assembled.
Historical scoped acceptance does not certify the new dependency closure.

## Start here

- `LEAN-HANDOFF.md`: project layout, exact pending interfaces, pinned dependencies,
  trust boundary, final replay procedure, and resource policy.
- `MATHEMATICS-HANDOFF.md`: self-contained mathematical model, all remaining
  original cases, substantial independent work assignments, current deductions,
  and failed shortcuts.
- `../audit/HANDOFF-C981-POSITIVE.md` and `HANDOFF-C981-NEGATIVE.md`: the frozen
  positive and complementary sign continuations for C981 vectors 34/41.
- `../audit/HANDOFF-C1092.md`: all four exact sectors, the unfinished opposite-pair
  argument, and the shared 48/573/574 entrance.
- `obligations.json`: current exact source-case and remaining-vector inventories.

## Measured size and validation

The preferred source closure plus three retained drafts is **343,370 Lean lines
in 4,352 project modules plus three draft files**, totaling 25,719,709 bytes.
No unexpected project import is missing. The three drafts have explicitly
recorded absent historical imports and are not active build roots.
The source census took about 2.2 seconds under a 256 MiB aggregate guard; it did
not start a compiler. It does not prove tactic success or theorem acceptance.

The approximate 300k assembly target is not met. No defensible final sub-million
source bound or completion ETA exists yet. Dependencies and actual checking
cost must be counted when evaluating the user's compilation-time limit.

For preservation, the Lean ZIP and branch also retain current unselected source
and alternate implementations. `source-inventory.json` separates this wider
snapshot from the preferred proof closure. Retaining alternate source does not
mean importing it into the proof. In particular, do not combine the preferred
C898 cached assembly with its legacy alternative.

`static-source-audit.json` records source-only token, import and hash checks,
Python syntax checks, inherited native decision sites, and documentation path
redaction. These checks are not Lean acceptance. `PUBLICATION-MANIFEST.json`
authenticates the exact source/document snapshot; each ZIP has its own manifest
and was checked for CRC and member-hash integrity.

## What was preserved and what was excluded

Preserved: all current `Compact`, `Completion`, and `source` Lean files, all
retained draft adapters, current scripts, mathematical audit notes, current
case contracts, useful provenance/summary manifests, and both detailed handoffs.

Excluded: external libraries/caches, compiler objects, duplicate vendor sources,
private original ZIPs, account/conversation logs, and historical raw or duplicate
generated intermediate payloads not imported by the preferred source.
`omitted-evidence-inputs.json` records the latter file paths and sizes; these
remain untouched in the original local workspace. Such inputs may be needed to
rerun historical recovery/proposal generators, but not to read or eventually
compile the retained preferred source. This is not an archive of the old
multi-million-line corpus under another name.

The mathematics ZIP deliberately contains relevant mathematical source, exact
contracts and evidence notes without the full generated build closure. Use the
Lean ZIP or the published project for actual Lean continuation.

## Publication safety and scope

Before publishing, the remote had no `12Refractored` branch and no
`codex/n12-compact-refactor` branch. The original
`codex/complete-twelve-squares` still pointed to the parent checkpoint above.
Thus the interrupted account-switch attempt had not published this refactor.
Publication uses a new branch; no original branch is overwritten or force-pushed.
The existing workflow is manual dispatch only; no CI or full compiler run is
requested by this checkpoint.

Keep local project storage below 10 GB. One guarded computational process group
at a time; parallel mathematical reasoning is allowed with clear ownership.
Do not generate large case fans or start bulk replay while mathematics is open.
Preserve the theorem, strictness and all original assumptions. No new admissions,
custom axioms or native proof shortcuts are allowed. The original inherited
`native_decide`/`Lean.ofReduceBool` trust remains disclosed in the handoffs.

Original n=12 sources: Jatloe. The user suggested Muhammad Maaz's
[SOS tactic article](https://mmaaz.ca/writings/sostactic.html); it is credited as
a possible discovery method. No tactic or certificate from it has been used in
this refactor.
