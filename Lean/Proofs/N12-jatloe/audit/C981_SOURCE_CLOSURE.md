# Bounded recovery of C981 catalogue dependencies

10 October 2026. Source recovery only; no Lean compilation or theorem acceptance.

Recovered `S12/Case976Domains.lean` from the authenticated beginning of the original historical source stream:

- 340,978 bytes, 2,793 newline-counted lines.
- SHA-256 `c3caefc7b02efa3ca595011c8fd8a64728f060b14e11c454e786510b27e08c43`.
- Exact canonical copy: `vendor/S12/Case976Domains.lean`.
- Identical active copy: `source/S12/Case976Domains.lean`.
- No existing modified core file or original repository source was overwritten.

The original manifest's SHA-256 was rechecked against the pinned source lock (`8ace39f009882c427bb0a52430ea0cfcf0dbd3fb78421cca18d2472b9af0f460`). The recovered file's size and digest match that manifest exactly. This is source identity, not a proof receipt.

## Recovery method and bounds

The public recovery branch does not expose the original ZIPs as independently accessible archives. It publishes a 4.07 GB tar+zstd stream in parts. A parent-authorized bounded recovery read only the first 4 MiB part, `source.part0000`, from recovery commit `98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8`:

- Git blob: `7ac0500287553ffdbcf7e0c5fbacff2bba333987`.
- Part SHA-256: `4a99c59aaaed81167623ec608f10dfa871d7f52315f0fb81a95197d4a09b18ef`.
- The whole part was hashed before any bytes were passed to the decoder.
- The zstd frame declares a 128 MiB window; aggregate actual RSS remained independently capped at 128 MiB.
- Successful recovery took 3.206 seconds; the resource monitor recorded a peak of 95,760 KiB for the process group.
- The monitor reports no remaining processes or cleanup errors.
- Only 340,978 unique source bytes were retained; canonical plus overlay copies use 681,956 bytes. Compressed parts were never saved.

Four direct authenticated attempts downloaded the same 4 MiB part, totaling **16,777,216 bytes**, below the renewed 64 MiB direct-download allowance. Earlier connector requests rejected binary files as non-UTF8 and returned no usable data; their actual server-side download volume is not exposed. The upper bound from their requested part sizes was 65,011,712 bytes, and the parent explicitly renewed the allowance before direct recovery. Initial direct TLS/404 failures downloaded no payload. Credentials were used through the existing repository helper, only in memory, and were not printed or saved.

The successful prefix ends inside `s12-to117/S12/Case983Domains.lean`. The expected truncated-stream diagnostic is preserved. **The complete archive stream was not verified.** Individual retained source integrity is established separately by its pinned per-file hash. The source reader did not use archive paths to extract arbitrary files and did not retain large/generated proof members.

Provenance is in `evidence/c981-original-restoration.json`; the last attempt's detailed receipt is `audit/prefix-source-restoration.json`, with resource evidence in `.verification/source-prefix-resources.json`. The bounded, narrowly scoped reader is `scripts/restore_small_prefix.py`.

## Remaining source gaps versus mathematical gaps

At this snapshot, `Compact.Assembly.Frontier` has 71 local modules in its explicit import closure and **no missing source imports**. It remains a conditional assembly skeleton: no `Obligations` instance supplying the global reduction and all exclusions is thereby produced.

`Compact.Cases.C981` reaches 84 local module names and still lacks these three originals:

| Missing original | Bytes | Pinned SHA-256 |
|---|---:|---|
| `S12/DirectSingleDomain.lean` | 2,279 | `bf6e08cd337399e02dc10b3af4de265c972daae9f0519acaedebe6af1ef4d990` |
| `S12/DomainEnumeration.lean` | 3,686 | `6234b259a2569cb4aa10134bfdfb79c6357e157440bd5a1e2cf4cc0ea7a19925` |
| `S12/MissingCornerBranches.lean` | 1,620 | `e79257b4dadd27605877231f54168607e7881bfd3ede9c9102e6f6ccda3db320` |

These modules appear after approximately 10.36–10.89 GB of uncompressed material in manifest order. They are absent from both new progress ZIPs, the inspected visible Git trees, and the targeted local filenames. Further early-prefix downloads were stopped because there was no good bounded recovery path to those later members.

The C981 agent separately removed the unused `ConditionalEnclosure` import from `Ownership`, preserving every declaration body and recording the source audit in `evidence/c981-ownership-import.json`. Its new V116 symbolic route therefore does not depend on this recovery of the full catalogue. This audit does not count that separate source change as a recovered historical module.

Recovering the remaining three files would restore source interfaces for domain/corner coverage; it would not itself finish C981. The original catalogue still needs accepted proofs for all representative exclusions and sound exhaustive coverage. Conversely, the file-recovery obstacle should not be described as a newly discovered counterexample or impossible geometric obligation. A fresh small proof of those exact domain/corner statements is a legitimate alternative, but would be new mathematical/Lean work requiring its own validation, not an authenticated copy of an unavailable original.
