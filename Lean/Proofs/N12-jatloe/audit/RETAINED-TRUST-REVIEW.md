# Retained import and trust review

The read-only GitHub refresh at **2026-10-11 08:02:42 UTC** returned all 22
branches. Every head is identical to the pinned 06:46:22 UTC snapshot. There
are no added or removed branches, so no changed commit tree needed another
download. Both timestamped JSON records are retained in this audit directory;
earlier pinned evidence was not overwritten.

The independent local source audit at **08:05:26 UTC** resolved the current
29 preferred roots plus the authentic C717 step 18 and C701 step 23 chord
pilots. The root manifest and every scanned source remained unchanged during
the completed scan. No local import was missing and no import cycle was found.

| Scope | Local modules | Lean lines | Source bytes |
|---|---:|---:|---:|
| Current 29 preferred roots | 1,339 | 312,715 | 20,423,015 |
| Additional chord pilot dependencies | 7 | 1,747 | 97,107 |
| Audited union | 1,346 | 314,462 | 20,520,122 |

These are source measurements of the stated closure, not final delivery size.
Pending bank, fan, and graph replacements are not counted as activated.
External libraries, unresolved draft adapters, and additional future proposal
roots are outside these numbers. The current selected closure is still above
300,000 lines.

After removing nested comments and quoted strings, the scan found no explicit
`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`, `mkSorry`,
`axiomDecl`, `evalExpr`, `ofReduceBool`, `ofReduceNat`, or `trustLevel` sites.
It found **2,572 `native_decide` occurrences in ten S12 modules**, and none
in the selected Compact source. Every native-containing source line matches
an original vendor line verbatim; AngleData64 and AngleData128 match their
original unsplit AngleData module. The exact sites and original hashes are
recorded in `retained-trust-source.json` and `retained-native-provenance.json`.

This is an explicit source trust inventory. It does **not** certify macro
expansion, prove the absence of indirect external axioms, validate external
compiled caches, or substitute for Lean acceptance and final theorem
`#print axioms` output. The original native certificate trust boundary remains.
Whole n=12 optimality and the pending whole historical exclusions are not
claimed by this review.

The two chord pilots are source-activated with exact proposal hashes in
`evidence/historical-chord-pilots-activation.json`. Their concrete certificate
replay is still pending at this audit checkpoint; the generic AxisSection and
IndexedChord soundness modules have parent-confirmed successful replays.
