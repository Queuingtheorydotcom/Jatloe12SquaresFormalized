# Bounded recovery and replacement of missing geometry

Audit date: 2026-10-10. No archive binaries were downloaded, no historical
source bundle was extracted, and this worker ran no Lean compilation.

## Authenticated missing sources

The historical source manifest records:

| Original source | Bytes | SHA256 | Private source archive |
|---|---:|---|---|
| `S12/SquareAxes.lean` | 5,287 | `16ba019e7f7880c127733aefa31832a5db8460c8562b636e59ff18ecc2c8406c` | `s12-lean-progress-part-3.zip` |
| `S12/LongChordGeometry.lean` | 4,052 | `d48e8bebd3ec6fe9bedf80e0319138f792b1884450596a6c76d4ed0d7fbfa48d` | `s12-lean-progress-part-2.zip` |

Part 3 ZIP: 270,233,742 bytes, SHA256
`8ccb97d2b7b4e3294e74716c5aa33b297464377b6055fc76936d1ba82d30d9ec`.
Part 2 ZIP: 390,550,805 bytes, SHA256
`9be2de3a57fee072b2abf080e751075d38f9c67321461fe38e39c5dfa427b094`.

The metadata is in the old checkout's
`projects/n12-jatloe419/provenance/source-manifest.json.gz` and bundle
provenance. These files are not present as individual source blobs in the
11 inspected source-branch trees, the local Codex source inventory, or the
targeted ZIP inventories. The partial-work ZIP's
`recovered/source-payloads/lean-fragment-index.json` explicitly lists
SquareAxes among referenced modules without a literal recovered source;
LongChordGeometry is absent from that index.

## Why the 4 GB bundle was not restored

The public recovery snapshot is commit
`98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8` in
`EvolvingPrograms/SquaresLean`, under `historical/n12-lean-2026-09`:

- [README](https://github.com/EvolvingPrograms/SquaresLean/blob/98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8/historical/n12-lean-2026-09/README.md)
- [Provenance](https://github.com/EvolvingPrograms/SquaresLean/blob/98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8/historical/n12-lean-2026-09/provenance.json)
- [Bundle manifest](https://github.com/EvolvingPrograms/SquaresLean/blob/98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8/historical/n12-lean-2026-09/bundle.json)

The original private archive wrappers are not redistributed. The published
payload is a single deterministic tar+zstd stream split into 355 binary
parts: 4,066,975,006 compressed bytes, SHA256
`fb9feedf4392ca70fb6f5a336bf331319e71fde5317c08993b406c1baea144ee`.
Its restore procedure streams and expands the complete payload. This is
not an HTTP-range-readable ZIP with a central directory and independently
compressed source members. No authenticated standalone private-ZIP URL was
found. Metadata-only recovery stayed below the 10 MB request budget.

The new `Compact/Bridge/BorderEndpoint.lean` does not require either missing
file. Its 12-module original-model dependency closure is already resident.

## Small replacement for the SAT dependency

The current repository has a separate scalar proof at commit
`c5c6144349a141e56ac43c81ed732f731c591eac`:

- [Intervals](https://github.com/EvolvingPrograms/SquaresLean/blob/c5c6144349a141e56ac43c81ed732f731c591eac/Lean/Squares/Separation/Intervals.lean)
- [Positive orientation](https://github.com/EvolvingPrograms/SquaresLean/blob/c5c6144349a141e56ac43c81ed732f731c591eac/Lean/Squares/Separation/Positive.lean)
- [All signs and zero components](https://github.com/EvolvingPrograms/SquaresLean/blob/c5c6144349a141e56ac43c81ed732f731c591eac/Lean/Squares/Separation/Signed.lean)

These three scalar proofs were adapted only in their imports and namespace
into `Compact/Geometry/ScalarSAT{Intervals,Positive,Signed}.lean`.
The new `Compact/Bridge/CongruentSAT.lean` transports their overlap witness
through the original square's orthonormal frame and positive half-side.
The result derives `C977ChainBridge.FaceSeparation` directly from original
OpenSquare disjointness and equal side lengths. Equal side lengths are
already guaranteed by `NormalizedPacking`; no orientation or contact
restriction is added. The four weak alternatives include equality.

The replacement comprises 376 source lines before replay repairs, and
removes the need for the missing historical SquareAxes in normalized
packing applications. It does not reconstruct or claim the historical
general unequal-side theorem. Source assembly is not a Lean acceptance
receipt: the parent worker controls serial compilation and reports its
actual result. Long-chord replacement is independently owned by the
symbolic worker.
