# Cloud continuation, 14 October 2026

The user requested continuation from the paused checkpoint
`d5620c3a7eaa08943e0dbea2604e1079e2209238`. The tracked `PAUSED.json` marker
is removed for this resumed branch; the checkpoint branch retains its original.
The exact unrestricted `S12.packingConstant12 = 4` theorem remains unfinished.
The October 14 continuation guide remains the mathematical task map.

## Environment and resource policy

Lean 4.19.0 and the nine exact dependency revisions in
`dependency-pins.json` are installed. The focused library cache was restored
using the pinned Mathlib cache hash calculator, with TLS verification enabled.
No Mathlib source was rebuilt and no dependency declarations were changed.

The receiving Linux cloud machine has four CPU cores and 32 GiB memory.
The initial 900 MiB aggregate guard stopped while loading `S12.Diagonal`.
The explicitly selected cloud budget is 2048 MiB aggregate RSS, 180 seconds
per focused invocation, and a 3 GiB free-space floor. Run one guarded compiler
group at a time, with one Lean worker. Never raise this budget silently.
All stopped groups must report no surviving processes or cleanup errors.

Keep total source, Git metadata, toolchain, dependency cache and outputs below
10 GB. The current source census remains 7198 modules including external
libraries, below the preferred 8000 and hard 10000 limits. This census does not
include unwritten future proofs and does not establish global acceptance.

## Focused continuation

From `projects/n12-refactored`, inspect the source census before each replay:

```sh
mkdir -p .verification
python3 -B scripts/source_census.py
python3 -B scripts/bounded.py --rss-mib 2048 --seconds 180 --free-gib 3 \
  --receipt .verification/cloud-angular-resources.json -- \
  python3 -B scripts/verify.py Compact.Completion.C981.AngularScalars
```

The first focused replay accepted `Compact.Completion.C981.HalfAngle` and
`Compact.Geometry.C977CornerCubic`. It reproduced the seven recorded
`AngularScalars` failures and rejected that candidate, including its resulting
admission warnings. No failing object is accepted as a proof. Subsequent repair
commits must include their actual scoped replay and axiom audit results.

Keep machine-specific diagnostics and source-hashed receipts under ignored
`.verification`; keep compiler objects under ignored `.lake`. Follow the
existing semantic, ownership, boundary, trust and whole-case acceptance rules.

## Accepted first repair

The repaired `Compact.Completion.C981.AngularScalars` root passes the serial
verifier with no admissions. Its three-module local closure now contains
`HalfAngle`, `C977CornerCubic` and `AngularScalars`, rather than the previous
ten-module closure through wall geometry. The final root compilation took
6.776 seconds; the guarded invocation used approximately 1059 MiB peak RSS.
These measurements describe this focused check, not a complete-proof estimate.

The five exported half-angle lemmas were checked with their full statements and
`#print axioms`. The repaired `AngularScalars.impossible` axiom query reports
only `propext`, `Classical.choice` and `Quot.sound`. No new native decision,
admission or geometric assumption is introduced. The global theorem and the
whole-vector adapters remain open until their respective replays succeed.

## Accepted last-cycle scalar repair

`Compact.Completion.C981.LastScalars` now passes its four-module scoped replay
with no admissions. The two reproduced failures are repaired by the same exact
polynomial sign argument and explicit transitivity of the endpoint inequalities.
The exported `half_endpoint_refined`, `half_endpoint`, `marker_cut_small` and
`negative_impossible` statements retain their original hypotheses and conclusions.
All four axiom queries report only `propext`, `Classical.choice` and `Quot.sound`.
The final root compiled in 7.583 seconds under the same cloud guard, with no
surviving processes or cleanup errors.

These scalar repairs do not yet establish acceptance of `CommonRows`, `Common107`,
`LastRows`, `Last104` or the whole C981 registry. Their larger original-packing
closures and the remaining case contracts still require their own replays.

## Accepted shared short-cluster replay

The C981 certificate-bridge replay reached its 180-second time guard at the
shared `S12.ShortCluster` dependency. The four-module `S12.ShortCluster` closure
now passes its scoped replay: the root compiled in 99.894 seconds, with no
admissions. Its public statements and all 64 excluding-face combinations in
each of the three templates are unchanged.

The projection bounds now follow from the existing squared-length identity and
standard absolute-value lemmas. The template proofs clear rational denominators
in shared hypotheses before splitting faces, then use the dense linear solver
with explicit premises. Every resulting proof is still checked by Lean.
The four exported declarations report only `propext`, `Classical.choice` and
`Quot.sound`. No native decision or geometric assumption is added.

This establishes the shared geometry module, not the C981 certificate data,
vectors 54/55, or the global theorem. The bridge replay must resume from its
hash-validated dependency receipts before those original adapters can count.

## Accepted compact certificate bridge

`Compact.Completion.C981.ShortCertificateBridge` now passes its complete
59-module scoped replay with no admissions. The root compiled in 1.503 seconds
after receipt-validated dependencies were prepared in bounded batches.
The two checkpoint type errors were caused by shadowed membership witnesses
after `List.mem_map.mp` and substitution; the repaired proofs name the raw row
membership and original index membership distinctly.

All eight public theorem statements are unchanged. Their full type and axiom
queries report only `propext`, `Classical.choice` and `Quot.sound`. Strictness,
positive denominators, angle witnesses, original side bounds, all eight overlap
axes and both cut/complement branches retain their existing definitions.

The finite `ShortCertificate54` data and the original vector 54/55 wrappers
still require their own replay. Acceptance of the generic bridge alone does
not discharge either original-vector obligation or the global packing theorem.

## Generated short-certificate replay remains unaccepted

The `ShortCertificate54.Original` closure contains 134 local modules. Its pinned
library cache was restored for 1,158 external modules without rebuilding Mathlib.
`S12.AngleData32` passed, but the 1.62 MB `ShortCertificate54.Inputs` initializer
has not passed. The default worker stack aborts in enabled syntax linters.
A supported 64 MiB worker-stack diagnostic avoided that immediate failure but
hit the explicitly selected cloud guard: 2,560 MiB aggregate RSS, 300 seconds,
and a 3 GiB free-space floor. It stopped at 252.068 seconds with approximately
2,563 MiB peak group RSS, no surviving processes and no cleanup errors.

The temporary stack, linter and namespace-scope experiments were reverted.
The verifier, generated data and generator retain their original contents and
checks. No failed object is accepted. Do not repeat the same large initializer
under a larger budget without a new diagnosis; investigate smaller generated
modules while preserving exact numerical payloads, names and public contracts.
The whole-source census remains 7,198 modules including libraries. Vectors
54/55, all nineteen remaining whole-case obligations and global optimality
remain open. Machine-specific diagnostic receipts remain in ignored
`.verification`, rather than this portable handoff.

## Accepted factored short-certificate inputs

The local continuation factors the exact `ShortCertificate54.Inputs` source
into metadata and 44 atom chunks, with at most 512 atom declarations per chunk.
The original public import and every public declaration name are retained.
The inverse audit reconstructs the checkpoint initializer with SHA-256
`b0fc08cdba764f59ca326dd99711fe0ff3cf639a7a851f8d09a1857fc3ca0038`:
17,987 rows, 2,711 denominators and 772 vertex bases. No numerical payload or
geometric contract changes.

The producer now reads ownership labels from the public Lean
`Completion.Cases.C981.VectorData` catalogue, rather than an absent private
handoff file. Regeneration reproduces the committed certificate exactly. It
finishes in 16.217 seconds, within the unchanged internal 25-second limit and
256 MiB memory guard. The generated corpus, including the bridge, contains
65 modules and 5,149,310 source bytes, within the six-MiB source limit.
The local generator module cap increases from 20 to 65; the whole current
proof census is 7,243 modules, including 2,456 external modules, with no
missing external sources. Future unwritten obligations remain uncounted.

`Compact.Completion.C981.ShortCertificate54.Inputs` passes its entire
106-module scoped replay with no admissions. Dependencies were accepted in
serial bounded batches and reused only after the verifier's source,
dependency, object and log hash checks. The final aggregate root compiles in
1.784 seconds. Every proof invocation keeps the 2,048 MiB aggregate RSS /
180-second guard, one Lean worker, default worker stack and enabled linters.
The verifier and dependency pins are unchanged.

A separate audit checks 76 public types and 70 axiom queries. The 32 exact
reference equalities depend only on `propext`; the validity declarations and
sampled row, denominator and basis declarations are axiom-free. All 106 local
replay sources match the Git checkout byte for byte. Receipts and build
objects remain in ignored directories, with persistent local backups.

This accepts the factored input data. The remaining generated initial/stage/
pair modules, both full original vector 54/55 adapters, all nineteen remaining
whole-case obligations and unconditional global optimality still require
acceptance. Resume with `ShortCertificate54.Original`; do not count the input
replay as a vector exclusion.

The first continuation of `ShortCertificate54.Original` reaches `Initial0`
and stops at the unchanged aggregate RSS cap after 10.961 seconds, with peak
group RSS 2,133,060 KiB, no surviving processes and no cleanup errors. No
initial-program object is accepted. The next compact step is to factor the
initial angle programs into independent modules, importing only their exact
row/denominator chunks and metadata, with an inverse audit of their original
declarations. Preserve the kernel numerical checks and original public names.
