# Historical JSON storage

Prepared on 2026-10-11. The compression script has been source-reviewed and
AST-checked, but this note does not assert that it has run or recovered space.

`scripts/compress_historical_json.py --run` applies only to JSON under
`evidence/historical/data`. It streams each original to deterministic gzip,
reads the compressed result back completely, verifies the original SHA-256
and byte length, syncs the result and verification journal, and checks that
the original file has not changed before unlinking the plain copy. A failure
retains the original or its verified compressed counterpart. The current
temporary file is removed on a handled failure.

The script has a 128 MiB memory limit, 115-second working deadline, 64 MiB
per-file temporary limit, and 2 GiB free-disk floor. It requires the parent's
serial resource slot. A stopped run can be resumed; existing gzip files are
verified rather than overwritten. The durable journal and last-run result
are written under `evidence/historical-json-compression`.

`scripts/provenance_source.py` resolves the unchanged logical source path to
the plain file or its gzip copy. It exposes byte/text reads, streaming reads,
and an existence check. Uncompressed hashes retain their original meaning.
Already-long filenames use a deterministic short name in the same parent's
`.provenance-gzip` directory rather than exceeding the filename limit.

Reader changes cover the three direct four-square scripts, six audit adapter
scripts, the manifest-driven historical direct-cover stream, and the numeric
record inventory. Their mathematics and output certificates are unchanged.
No original user archive, active compact certificate, Lean source data, or
historical log is selected for compression.
