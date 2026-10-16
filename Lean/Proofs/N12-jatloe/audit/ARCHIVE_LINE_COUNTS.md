# Authenticated historical Lean line counts

These are actual newline-byte counts read from the historical tar stream,
not an extrapolation from source bytes. Every counted Lean member matched
its manifest SHA256. All historical hashes used by the seven accepted case
receipts matched as well. This is source measurement, not a Lean replay.

| Historical source scope | Modules | Bytes | Lines |
| --- | ---: | ---: | ---: |
| C701 accepted closure | 253 | 339,882,452 | 434,692 |
| C713 accepted closure | 222 | 266,110,547 | 718,434 |
| C717 accepted closure | 295 | 459,733,372 | 1,434,523 |
| C898 accepted closure | 195 | 188,138,692 | 221,469 |
| C973 accepted closure | 245 | 333,362,494 | 684,347 |
| C978 accepted closure | 224 | 268,472,356 | 298,848 |
| C979 accepted closure | 298 | 331,494,096 | 1,473,106 |
| Deduplicated seven-case union | 938 | 2,119,721,626 | 5,121,803 |
| Original 117-to-18 closure | 7,496 | 3,734,670,747 | 3,817,003 |
| Deduplicated union of both scopes | 8,236 | 5,660,148,876 | 8,732,801 |

Each single-case count excludes its three small completion modules. The
seven-case union excludes 15 distinct completion modules. Their hashes are
listed in `ARCHIVE_LINE_COUNTS.json`; do not describe the table alone as the
complete project source total. Library dependencies are also excluded.

Across the whole historical archive, 63,024 complete Lean files were read,
totaling 22,152,201,879 bytes and 34,532,528 lines. The only uncounted Lean
member is the later 585-byte `scripts/CompareNativeMetadata47.lean`. All S12
source files and the two archived recovery fragments are covered. The
archive was intentionally stopped after the requested C898 data, so a whole
stream verification is not claimed.

Exact per-file measurements are in `archive-lean-source-counts.tsv`; scoped
sets, missing members and receipt-hash comparisons are in
`ARCHIVE_LINE_COUNTS.json`. These measurements supersede earlier unknown
line-count estimates for those same historical closures. They do not count
new completion branches, the 166,074-file C976 worker archive, user ZIP
contributions, or local C696 work, which have separate inventories.
