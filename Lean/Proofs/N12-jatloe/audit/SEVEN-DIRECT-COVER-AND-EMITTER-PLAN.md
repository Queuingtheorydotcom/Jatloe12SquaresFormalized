# Seven direct initial covers and remaining preservation data

Snapshot: 2026-10-11. The exact Python audits succeeded for all seven original
initial covers. This is finite evidence for new Lean checker instances, not
acceptance of seven new whole-case exclusions. The parent has separately
accepted the general planar-vertex theorem; checker/adapter replay remains
its own requirement.

## Exact initial-cover result

| Case | Actual owner entrances | Angle roots | Empty / absent-target roots | Reduced target poses | Nontrivial target-row occurrences | Nonparallel boundary pairs |
|---|---:|---:|---:|---:|---:|---:|
| 701 | 12 | 768 | 26 | 742 | 5,584 | 347,136 |
| 713 | 9 | 1,152 | 94 | 1,058 | 7,910 | 607,232 |
| 717 | 11 | 1,408 | 58 | 1,350 | 10,454 | 671,744 |
| 898 | 11 | 704 | 74 | 630 | 4,714 | 319,488 |
| 973 | 11 | 704 | 5 | 699 | 5,589 | 292,608 |
| 978 | 9 | 576 | 10 | 566 | 4,537 | 253,952 |
| 979 | 12 | 1,536 | 45 | 1,491 | 11,544 | 643,584 |
| **Total** | **75** | **6,848** | **312** | **6,536** | **50,332** | **3,135,744** |

Every target-row check and every empty-root check passed; the six-case report
has zero unsupported routes. It completed in 81.515 seconds. The C898 audit
completed separately. There are 76,850 feasible arrangement vertices across
all seven; these are occurrences, not globally distinct stored vertices.

The row column removes exact duplicates within each target and omits strictly
positive constant tautologies. The original C898 audit includes 630 such
constant rows in its 5,344 target-row count; its shared pose map gives the
harmonized 4,714 nontrivial rows used above. No rational positive-scale sharing
across targets has been credited here. The 6,536 reduced target poses already
belong to the subsequent continuous route, so a compact assembly must share
them with the pair/chord stages instead of storing a second initial copy.

Evidence: `evidence/historical-direct-cover-audit.json`,
`evidence/c898-direct-cover-all.json`, and
`evidence/c898-shared-pose-map.json`. Each audit records authenticated original
inputs. Angle64 is used by 701/898/973/978; angle128 by 713/717/979. Inside and
outside points, actual owner masks, original reduced domains, the side bound
`1 < side ≤ 1001/1000`, open forbidden rectangles, and all closed angle endpoints
are retained. The audit never filters strict boundary vertices to infer
emptiness.

## Why the old 9,024 count has a different scope

The earlier `seven-source-inventory.json` counter named
`tree_root_occurrences` increments for **every `regionTreeFromText` string in
the complete historical import union**, not for the selected seven current
initial cover interfaces. That union contains 938 modules, including
`Push972` (41 modules), `Push975` (28), and two `PushAuxTree976...` families
(24 and 11), in addition to the seven case families. Their old forests can be
pulled in by a shared helper even when not used in the new case entrance.

The exact difference is 9,024 − 6,848 = **2,176 roots**, now fully
reconciled by both completed post-forest scans: C972 contributes 576, C975
576, and the two C976 auxiliary families contribute 512 each. There are no
non-root tree strings in this count. Every selected current root was found.

The second authenticated 938-module pass records **642,781 pair certificate
declarations**, including 394,023 encoded certificates in C717/C979. Its
120,872 distinct rows, 29,321 distinct poses, 5,876 distinct literal blocks,
13,057 contexts and 129,600 context-row memberships describe a partial
retained-data closure: 17,946 pair bindings refer to predecessor target poses
that the original case-local selection omitted. Those definitions are present
in the recovered authenticated source. The parser now retains such literals
lazily and materializes only poses actually referenced by a current plan;
its next output must establish closure before these counts become a budget.

There is a further, material dependency: C701 Steps 0–3 reuse complete
predecessor plan lists (one step from each C976 auxiliary family and C975
Steps 1–2). Their pruning certificates remain necessary even though their
initial forests are replaced. The prepared compact-data emitter follows the
actual Plan-list aliases and checks the original source/neighbor equalities
and outgoing target membership. It distinguishes retained imported pair
checks from unused imported declarations. Thus 642,781 is not yet the final
pair-check count for complete preservation.

The 1,511 nonliteral `BlockRows` declarations refer to chord blocks' `.region`
fields. They are preserved as explicit chord obligations, not counted as empty
regions. `UnitAngleReference` is exactly `w.reference 1`, so the encoded
128-angle certificates preserve the original inner reference square.

Evidence: `evidence/postforest-source-inventory-v2.json`. These are source
counts and exact binding observations, not successful geometric certificate
checks or a complete Lean assembly.

## Consequence for the size argument

The old obstruction based on 230,414 rows plus 194,536 tree nodes plus 42,393
poses assumed a direct translation of the historical forests. That is no
longer the proposed representation. It must not be quoted as a lower bound on
the new direct-cover route. Nor can all those objects simply be subtracted:
rows can be shared with later stages, and the old union contains predecessor
proofs and other required helpers. The post-forest pass must count the actual
retained union.

What is already measured is the complete initial-cover shape: 75 point-premise
entrances, 6,848 angle records, 312 explicit empty results, 6,536 shared target
poses, and 50,332 nontrivial per-target row occurrences. The boundary pairs and
vertices are **checker computations**, not data that need one emitted witness
each. The initial forests, their old leaf contexts, and their incoming
relaxation witnesses are unnecessary for this direct initial interface after
its Lean instances and original-model adapters pass.

A compact implementation should have one generic root constructor and a data
table of selected original input indices and optional shared target IDs. The
inside/outside points are stored once per owner. Avoid repeating thirty lines
of definitions/theorems for every root: even seven thousand tiny wrappers would
consume the preservation budget without mathematical content. Use bounded
owner/angle batches with opaque checked tables, retaining readable records and
complete closed-grid coverage. The required batch size must be measured by the
parent's serial compiler, not assumed from Python timing.

## Source-conversion design for the other six

The six historical chains have 31, 10, 19, 28, 16 and 30 ordered operations
respectively; these include non-pair operations and are not constant-size
certificate counts. C713 remains the smallest next whole-route pilot. The
prepared inventory records exact transition statements and unsupported schemas
before any common emitter is generalized.

1. **Entrance and original contract.** Extract the necessary certified owner
   domains, common compulsory points and their proofs at declaration level.
   Preserve their inherited trust boundary and actual mask/row identities.
   Importing a bundled historical module to get one helper would reintroduce
   its forests. The existing C898 `PointPremises` adapter is the model, but each
   other case's entrance must be bound and checked explicitly.
2. **Shared remaining poses.** Retain actual reduced Initial poses and every
   later Step pose used by the complete chain, including branch pieces and
   outputs. Store exact rational rows with strictness once, with positive
   denominator or a proved positive-scale equivalence. Preserve original
   angle declarations and pose row order at the semantic adapter boundary.
   Remove raw `leaf{case}_...` and incoming links only because the new direct
   theorem reaches the identical reduced target list.
3. **Cached support geometry.** Use the existing `VertexSupport` /
   `CachedSupportFan` representation owned by the branch worker. Each two-row
   basis stores its exact integer intersection and positive denominator once.
   Its row identities and context memberships are checked once; requested
   directions must pass the nonnegative-cone and strictness checks. Pairing
   two supports then checks the original separating-axis constant/slack.
   No geometric optimality of the proposed fan is trusted.
4. **No per-pair witness duplication.** A source plan stores its blocked region,
   source pose and complete neighbor domain. Fan lookup supplies candidate
   bases for every required axis and neighbor; the kernel still checks all
   of them. Avoid serializing four row indices eight times per pair. The C898
   all-pair evidence has 25,843 pairs but 1,063 contexts and 10,072 context-basis
   memberships. Those are measured C898 counts, not ratios to extrapolate to
   the other six. Their exact contexts and fan sizes need their own audit.
5. **Actual angles and degeneracy.** The six cases use both 64- and 128-bin
   grids; later poses may use other explicit grids until the schema inventory
   resolves them. Direction IDs must map to exact signed normal vectors, not
   reuse a hard-coded `angle mod 64` convention. Preserve strict inequalities.
   Empty or degenerate contexts may need an exact empty certificate or another
   supported fallback; a failed two-row basis is not an allowed assumption.
6. **Complete transitions.** Reconstruct first-false-row pruning and all closed
   split ties, exact result-piece lists, and outgoing relaxations. Preserve all
   source poses and every needed neighbor. Chord/window transitions retain
   their actual section/radius premises and original neighbor domains; do not
   label them pair steps. Unsupported refresh, ownership or chord schemas are
   explicit blockers to conversion, not omitted costs.
7. **Assembly and measurement.** Compose the ordered original chain to its
   final empty owner, then bind `ExcludesCase id`. Measure the actual shared
   source union, serialized bytes, objects, whole checking time and both memory
   measures. Only successful full case replay makes the replacement accepted.

This design supplies a concrete route to a much smaller preservation corpus,
but not a completed 300,000-line assembly or a sub-million-line global proof
bound. The remaining unmeasured categories are cached basis/fan records,
complete transition data and fallbacks, outgoing relaxations, chord/window
certificates, original entrance dependencies and final semantic bindings.
