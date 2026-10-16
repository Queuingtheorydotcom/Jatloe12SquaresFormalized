# Complete-proof size accounting

> **Superseded size snapshot.** Use [the current status](ENTIRE-FORMALIZATION-STATUS.md) and [the current size/translation report](REMAINING-SIZE-OBLIGATIONS.md). The preferred 28-root census is 306,487 lines before the newest small additions; resident active/draft source is 518,110 lines. The 58 original exclusions are accepted and 59 remain. The bank, direct-cover and shared-point reductions have advanced, but compact preservation of the six historical cases is incomplete until all 64 entrances and 134 stage fields are filled. Do not use the old 177k/227k closures, older bank packaging or allocations below as a completed delivery or final source bound.


Snapshot: 2026-10-11 04:15 UTC. **Neither preservation of all completed work
within 300,000 Lean lines nor a complete proof below one million lines is
established.** The current source assembly is substantially smaller than the
historical corpus, but unfinished translations and mathematical gaps still
have to be counted. No total below extrapolates a single leaf or case.

## Current source assembly and exact remaining scope

The preferred proof-bearing registry starts from the unchanged 117 original
case contracts. Six symbolic families provide source terms for 58 whole-case
exclusions. The exact complement contains 59 cases: twenty capacity-route
baseline cases, twenty-one other baseline cases, seven historically accepted
late cases, and eleven other late cases. Its source/import replay is still the
acceptance boundary. Full original contracts and IDs are in
[REMAINING-PROOF-PLAN](REMAINING-PROOF-PLAN.md).

| Explicit source roots | Local modules | Lean lines | Source bytes |
|---|---:|---:|---:|
| `Compact.Assembly.SymbolicRegistry` | 185 | 20,418 | 1,645,187 |
| `Compact.Cases.C898.Complete` | 268 | 165,094 | 16,047,127 |
| Union of these, `C981V116`, `C977WallCenters`, `C981WallCenters` | 401 | 177,823 | 16,659,574 |

These are the read-only import-closure snapshot recorded in the remaining-proof
plan. They include imported local `source/S12` and `Completion` modules, but
exclude pinned Lean/Mathlib sources and unused provenance archives. They are
not a final fresh replay receipt. Older budget JSON files refer to different
roots and revisions; the previous 164,522-line C898 count is superseded here.

C898 has complete source for the original entrance, all 704 angle roots,
1,121 leaf links, thirteen pair stages, two chord stages and final contradiction.
It remains in the 59-case complement until accepted. No deliberately missing
mathematical premise remains in that source. Its full replay is pending; recent
focused passes for `SharedRows` (6.536 seconds), `SharedPoses` (12.970 seconds)
and production `AngleData64` (4.336 seconds) do not replace that replay.

## Completed selected recovery

The selected recovery is complete. It recovered all 2,533 requested new files,
with 889 previously authenticated files retained, and no missing selected
targets or reported decoder errors. It retained 987,740,538 additional bytes,
including compressed historical Lean provenance, after streaming
4,066,975,006 compressed archive bytes. The authenticated source union covers
all seven historically accepted exclusions: 701, 713, 717, 898, 973, 978, 979.

The guard receipt records 435.721 seconds and 328,624 KiB peak aggregate RSS,
with no cleanup errors or remaining processes. Each selected file was checked
against its expected hash. Recovery stopped after all selected targets were
recovered; the complete compressed archive stream was not verified, and this
does not claim authentication of every unselected archive member. In
particular, 363 exploratory region files were deliberately omitted. Recovery
executed no archived checker and performed no fresh Lean acceptance.

Evidence: [selection](SELECTED_PROGRESS_RECOVERY_PLAN.json),
[restoration receipt](remaining-progress-restoration.json), and
`.verification/selected-progress-recovery-resources.json`.

The old partial numerical inventory's claim that 97.99% of intended numerical
bytes were absent describes an earlier interrupted selection. It is not the
current blocker for the seven accepted exclusions. Their complete original
source witnesses are available; selected numerical inputs and generator sources
are also available for inspection. This does not mean every exploratory record
or every unfinished case has a complete accepted certificate.

## Exact inventory of all seven historical source closures

The structural pass authenticated and inspected all 938 modules in the union,
with zero missing source files. It compared complete canonical values when
sharing records; hash-only matches did not establish equality.

| Inventory item | Exact count |
|---|---:|
| Historical source modules | 938 |
| Historical uncompressed source bytes | 2,119,721,626 |
| Historical source lines | 5,121,803 |
| Distinct affine rows, including strictness | 230,414 |
| Distinct tree syntax nodes | 194,536 |
| Distinct tree syntax roots | 5,544 |
| Distinct poses | 42,393 |
| Distinct weighted-row lists | 106,991 |
| Distinct forbidden blocks | 6,244 |
| Pair-candidate declarations | 283,495 |
| Unsupported declaration schemas | 1,603 |
| Source lines untranslated by this structural pass | 3,323,189 |

Evidence: [seven-source-inventory.json](../evidence/seven-source-inventory.json).
All source coverage completed and the report was written before final reporting
expanded large diagnostic dictionaries and the external 384 MiB guard stopped
the process. The outer receipt records a 395,216 KiB peak, 61.383 seconds, and
clean process cleanup. Therefore the source coverage result is complete, but
this was **not a successful bounded end-to-end process run**. The reporting
implementation has since been reduced; no completed replacement run is claimed.

This pass did not request the full pair-reconstruction check. An empty
`pair_failures` list therefore means no such pass ran, not that all 283,495
candidates were verified. Untranslated lines include source structures and
semantic bindings beyond the implemented parser; they must not be silently
excluded from the preservation budget.

Rows, tree nodes and poses alone total **467,343 distinct records**. A direct
one-record-per-line representation already exceeds 300,000 lines before pair
supports, relaxations, chord data and case bindings. This is an obstruction to
that representation, not a lower bound on a different mathematical proof.

## What has actually been compressed

The C898 conversion supplies concrete, whole-route measurements:

- Shared per-angle dictionaries reduced initial rows from 44,584 to 29,524.
- The checked context traversal removes 41,616 serialized context records,
  deriving each child context from its actual parent cut.
- Exact forbidden-block membership removes 14,088 tautological implication
  certificates while retaining every branch and all 1,121 leaves.
- All 25,843 pair certificates in thirteen pair stages were reconstructed from
  four row indices with zero fallbacks. The generic soundness theorem passed;
  this finite reconstruction is not a result for the other six cases.
- All 2,048 relaxation links have reconstructed supports, including 24,126
  two-index support occurrences and 15,504 distinct checks. Their complete
  case composition still needs replay.

The earlier 124,996-line initial cover stored explicit contexts and has been
superseded by the traversal assembly. It should not be added to the new source
union or used as the preferred remaining cost.

A later primitive-row/empty-basis inventory stopped safely after only 175 of
938 modules. Within that partial scope, 15,048 empty witnesses were checked:
14,623 used two rows and 425 used three, with no failures. Its 56,335 rows and
4,069 poses did not shrink under the implemented normalization in that scope.
These observations are promising or limiting only for those inspected inputs;
they are not global savings factors. The partial report is
[seven-source-inventory-primitive.json](../evidence/seven-source-inventory-primitive.json).

C977's new symbolic source restriction leaves 57 vectors in four wall branches,
228 contexts, instead of 912. This is a reduction in remaining original contexts,
not a whole-case exclusion. Its research DAG separately reduces 5,619 selectors
to 4,413; selectors are not certificates and supply no independent line bound.
C981 V116 and its uniform residual center cuts likewise do not remove the
remaining original case981 contract.

## Constructive budget gates

An honest final bound must assign every original ID either a checked small
whole-case exclusion or a complete finite certificate object with all original
coverage and semantic bindings. Sum the actual serialized dependency union
once, including rows, support terms, cuts, ownership/symmetry links, relaxations,
chords, terminals and fallbacks. Count bytes, semantic records, object sizes and
checking cost as well as source lines. Line packing and hidden archive imports
do not meet the efficiency requirement.

The following allocations match the remaining-proof plan. They are development
limits that trigger reassessment, **not forecasts or proved upper bounds**.

| Incremental scope | Proposed line allowance | Current confidence |
|---|---:|---|
| Shared foundation, symbolic adapters, geometry/checkers and assembly | 50,000 | Current registry closure is 20,418 lines; further shared work must be counted. |
| All seven historical exclusions' additional data and adapters | 250,000 | High risk; the current direct structural representation does not fit. |
| Forty-one remaining baseline cases | 150,000 | Unmeasured; needs substantial grouping or compact complete traces. |
| C696 / C709 / C974 | 50,000 | Entrances and coupled mathematical gaps remain. |
| C976 / C983 | 120,000 | Highest ownership/branching risk; no wholesale translation. |
| C977 / C981 | 160,000 | Uniform cuts help, but remaining context implications are uncounted. |
| C1089 / C1090 / C1091 / C1092 | 70,000 | Missing dependencies and coverage prevent a reliable estimate. |
| Contingency | 100,000 | Does not weaken any proof obligation. |
| Proposed total ceiling | 950,000 | Attainability is not established. |

The next gates are full acceptance of the written registry and C898 source;
a complete primitive/support inventory with actual serialized output; and a
second whole historical-case pilot, preferably C713. If preserving the seven
misses its allowance, derive another whole coupled symbolic replacement or a
proved sharing scheme before expanding the corpus. The remaining baseline
families, merged central pairs and 849/851 are concrete mathematical targets.

Compiler pilots run serially under separate 1,800 MiB aggregate RSS and 800 MiB
physical-footprint caps, with elapsed-time/free-disk limits and cleanup. Do not
use an internal `-M` flag. Separate numerical jobs use 128–384 MiB caps. Total
local storage must remain below 10 GB. Report external dependency-cache and
compilation costs separately; the module cap is intended to control compilation
time, not just the number of project source files.

The outstanding blocker is now **compact preservation and missing mathematics**,
not a missing download for the accepted seven. No defensible final ETA or
sub-million-line guarantee follows from the current source snapshot.
