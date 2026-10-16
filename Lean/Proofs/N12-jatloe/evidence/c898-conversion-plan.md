# C898 complete-case conversion pilot

## What is already established

The inherited `evidence/C898/case-replay.json` records a scoped Lean 4.19 replay of
`S12Completion.C898.excluded`, `family_eq_original`, and
`S12.case898_shared_impossible`. Its axiom list includes `Lean.ofReduceBool`.
This is evidence for the previous complete C898 exclusion, not a replay of the
new compact project or a kernel-only conversion.

The current Git branch `n12/lean-4.19` has
`projects/n12-jatloe419/Completion/Cases/C898/Proof.lean`. That wrapper proves
`ExcludesCase 898` by applying `S12.case898_shared_impossible` to the unchanged
family. It contains no certificate details. The new conversion must deliver the
same original-square exclusion and preserve the exhaustive case-family input.

The receipt lists 198 modules. Of these, 195 match original source-manifest
entries, totaling **188,138,692 source bytes**. The 66 `Push898Chunk` modules
account for **186,698,185 bytes**. These totals exclude Lean/Mathlib and concern
the accepted closure, not every archived file whose name contains `898`.

## Obtain these records before converting

The historical manifest identifies the following exact files in
`s12-lean-progress-update-37-part-2.zip`:

| File | Bytes | Purpose to inspect |
| --- | ---: | --- |
| `data/region898.json` | 10,866,560 | Candidate unsplit region/certificate trace |
| `data/batch-Push898-manifest.json` | 155,534 | Original declaration/chunk mapping and coverage |
| `data/case898-input.json` | 8,670 | Original case-family input |

The region record's SHA256 is
`a266c789f036f9b67c92a631e254185c47dde24f913aac8e37ee887c35e6d442`.
Do not assume that region data contains all proof witnesses until inspected.

Four small checker sources from `s12-lean-progress.zip` describe the accepted
checker interface: `S12/DirectSingleDomain.lean` (2,279 bytes),
`S12/CompactRegionTree.lean` (2,170), `S12/CompactFarkasText.lean` (1,494), and
`S12/CompactPoseText.lean` (818). Their combined size is 6,761 bytes.

Direct GitHub reads on `n12/lean-4.19` succeeded for the completion wrapper but
returned 404 for those four original checker files, `S12/Push898Chunk0.lean`,
and both small data/manifest paths. None of these exact original files exists
in the inspected local project paths. This establishes the need for targeted
archive/research-pack access, not that the records are unavailable elsewhere.

## Concrete conversion sequence

1. Read the three data records and four checker sources through a targeted
   archive member or bounded research-pack fetch. Check the historical hashes.
   Identify the root coverage theorem, domain enumeration, and every terminal
   leaf kind. Check whether the region record carries the Farkas/support
   witnesses needed for the accepted theorem. If it omits them, retrieve only
   the original declaration groups identified by the batch manifest.
2. Traverse backward from the complete exclusion and retain only witnesses
   and states actually used by that root. Distinguish state identity from raw
   numerical equality: a node's owner, domain, and assumptions belong in its
   key. Preserve all exhaustive split/cover edges.
3. Replace repeated normalized rational support rows by primitive integer
   rows and positive normalization denominators. Clear certificate weights
   jointly. The existing `IntegerSupport` checker already proves soundness
   for a two-row step against the original `S12.LinearConstraint` semantics;
   extend the same construction to sparse finite sums if real C898 witnesses
   require more than two rows. Do not force every leaf into a two-row format.
4. Represent region nodes directly by references to prior nodes and persistent
   state updates. Prove each primitive's preservation once, then compose the
   shared semantic DAG. Do not decode a DAG back into an expanded tree. Keep
   certificate arithmetic in integer checks and reuse checked theorem terms.
5. Assemble the entire C898 root, including family identity and all original
   coverage obligations, before its Lean validation. The acceptance endpoint
   is `ExcludesCase 898`, with the original model and no added hypotheses.
   Audit its axioms; a kernel-only pilot must not inherit `Lean.ofReduceBool`
   through imported legacy certificate theorems.

## Measurable acceptance criteria and remaining uncertainty

Measure the complete replacement import closure's source bytes, source lines,
wall time and peak resident memory. Include data, wrappers and newly required
checker modules. Compare with the same original case scope; the small C696
support fixture is not a whole-case baseline.

The 10.9 MB record versus 186.7 MB of generated C898 chunk source is a reason
to investigate this conversion, **not a demonstrated 17-fold proof reduction**:
the formats may carry different information. Whole-case savings and a useful
ETA remain unknown until the trace schema and leaf witnesses are inspected.
The immediate blocker is access to these exact records, followed by verifying
that their witnesses cover the accepted complete exclusion.
