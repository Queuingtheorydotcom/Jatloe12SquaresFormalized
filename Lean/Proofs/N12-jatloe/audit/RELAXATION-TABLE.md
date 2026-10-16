# Relaxations from source and target pose IDs

Status: the generic checker, original-model bridge, materializer and authentic
first C898 link passed the parent's serial Lean replay. The bridge,
materializer and pilot took 1.308, 1.420 and 1.225 seconds respectively.
No numerical audit or Lean run was performed by this worker. The complete
927-link replacement is now activated as source and awaits full replay.

The parent ran the bounded producer in 0.014 seconds. Its exact result is
927 source/target records, 16 modules, 4,728 lines and 112,386 bytes. It stores
no support-rule dictionary, per-link support list or affine coefficients.
Every original retained link ID and endpoint matches the existing map.
`evidence/c898-compact-relaxation-activation.json` records the SHA-verified
source activation. The 25 prior explicit-support modules remain unchanged
and are also copied to `evidence/source-archive/c898-explicit-retained-relaxation`.
These are source-size measurements, not a full-table acceptance or timing.

The independent data of a relaxation are its source and target poses. Their
angle and all affine inequalities already exist in the shared dictionary.
The old support lists can therefore be omitted from Lean source whenever a
bounded local search reconstructs valid witnesses for every target row.

## Checked representation

`Compact/Core/RelaxationHints.lean` checks four small witnesses:

- A constant target follows from the universally true strict row `1 > 0`.
- A copied source row keeps its exact coefficients and strictness bit.
- One source row supplies a positive integer multiple plus nonnegative
  constant slack.
- Two source rows supply the existing Cramer certificate and constant slack.

Every referenced source position must be in bounds. Every target receives
exactly one witness, in original target-row order. The existing sparse integer
checker establishes coefficient identities, nonnegative weights, positive
scale and the strictly positive contribution required for a strict target.
No source default can satisfy a missing-position obligation.

`Compact/Bridge/RelaxationTable.lean` binds cached integer rows by exact
equalities to the existing `IndexedRelaxation.Dictionary`. Its soundness
theorem preserves the dictionary's original `PoseLeaf.OrientedRealizes`
predicate, full angle witness and positive-denominator normalization. Its
cover theorem requires a checked link for every source pose. All bounded
finite-ID decisions explicitly traverse the supplied lists.

`Compact/Core/RelaxationSyntax.lean` provides:

```lean
noncomputable def link : RelaxationTable.Entry dictionary :=
  cached_relaxation%(dictionary, sourcePoseId, targetPoseId)

theorem checked : link.Check := by decide +kernel
```

The elaborator reads closed row constructors, finds a witness, and emits only
ordinary data. It constructs no proof of its search result. Local row caches
are separately checked equal to the dictionary rows; the kernel checks the
selected witnesses, without replaying unsuccessful search candidates.
There is no `native_decide`, `evalExpr`, filesystem read, theorem oracle or
new axiom in the materializer. Local lists are limited to64 rows and the
conservative candidate bound to32,768 comparisons per link. Unsupported
targets stop elaboration with an explicit error.

## Authentic first obligation

`Compact/Cases/C898/RelaxationPilot.lean` uses original source1752 and
target1751, the historical `continuousScout898Step0Pose0Link0`.
The retained witness table currently assigns eight nontrivial support rules
to that link. The new source stores only its two original pose IDs, and its
soundness theorem concludes the same original oriented-pose implication.
This instance passed the parent's replay; it closes this exact implication.

## Whole-table migration

1. The hint checker, original-model bridge, materializer, and actual pilot
   have passed. Full-table elaboration and kernel costs remain unmeasured.
2. `scripts/prepare_c898_relaxation_table.py` prepares a proposal retaining
   the exact order of the927 non-incoming links in
   `evidence/c898-relaxation-two-index-witnesses.json`. Generate one source/target
   record per link, with ordinary numeric checks in batches of eight. It
   writes only `evidence/proposals/C898RelaxationTable` plus its report. Remove
   the support-rule dictionary and per-link support-ID lists from the new
   import closure. Keep the old link index mapping for consumers.
3. Export each checked entry's original source-to-target soundness lemma.
   Consumers should compose these lemmas directly or use the new complete
   cover theorem. They must not fake the old `IndexedRelaxation.Link.Check`
   interface with empty support lists.
4. Adapt the pair-stage and chord-stage callers without changing their source
   pieces, target domains, orientation witnesses or complete-source checks.
   Only then retire the old relaxation closure from the final deliverable.

The existing exact C898 audit found a two-row witness for every non-alias
target of all2048 historical links, including the927 retained ones. Thus it
is evidence that this route is applicable there, although materializer limits
and actual Lean performance still require checking. The new single-row rule
also handles the rank-one cases previously padded with an unused independent
source at weight zero.

## Scope of a wider source bound

The other six historical cases contain17,651 still-unrepresented relaxation
links. No complete scan establishes that every one has a two-row witness.
In particular, an inconsistent source may imply a target only through a
three-row refutation; it is unsound to assume that two rows always suffice.
Such cases need a checked higher-arity certificate or a mathematical
simplification. They remain explicit failures, never accepted defaults.

If a bounded exact scan succeeds, the independent Lean records become one
pose-ID pair per link, instead of all row-support indices or rational weights.
That is a concrete source representation bound for those links. It is not a
bound on object size, replay time, complete case closure, or the entire
300,000-line preserved-work target. Cache objects still contain the chosen
small witnesses; their actual costs must be measured.
