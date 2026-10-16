# C898: original geometry and a new short occupied-row reduction

This is a symbolic audit of the recovered original case, not a claim that
C898 has a new complete short proof. No search or certificate generation
was run for this audit.

## Exact original entry and provenance

The recovered `vendor/S12/Push898Chunk65.lean` retains the original module
boundaries and hashes. Its original `S12.Case898Domains` starts at line3217,
`S12.Case898RefinedDomains` follows the ownership theorem,
`S12.CommonPoints898` starts at line4606, and `S12.SharedCase898` starts at
line4796. The actual entry theorem at line4824 is
`case898_shared_impossible (p : NormalizedPacking)
(hf : codedMarkerFamily p = case898Family) : False`.
The family is `{1,2,12,16,192,768,1056,2048,4096,8192,16384,32768}`.

The common-point statements are certified consequences of the original
packing and finite ownership domains. They are not optional pose-enclosure
assumptions. Their original source uses 20 ownership-domain refinements,
then enlarges each domain to the displayed allowed auxiliary sets. A new
packing adapter must retain or replace that finite argument; merely
assuming the resulting common points does not discharge the original entry.

| Domain | Owner mask | Certified common closed points |
|---|---:|---|
| 0 | 1 | (1,.914),(1.87,.76),(1.74,1),(1.12,1) |
| 1 | 2 | (.76,1.87),(.914,1),(1,1.12),(1,1.74) |
| 2 | 12 | (3,.914),(3.086,1),(3,1) |
| 3 | 16 | (2.13,3.24),(2.26,3),(2.88,3),(3,3.086) |
| 4 | 192 | (.914,3),(1,3),(1,3.086) |
| 5 | 768 | (1.65,1.65),(2.35,1.65),(2,1.74) |
| 6 | 1056 | (2.35,2.35),(3,2.26),(3.086,3) |
| 7 | 2048 | (1.65,2.35),(1.74,2),(2,2.26) |
| 8 | 4096 | (.914,2),(1,2.26),(1,2.4) |
| 9 | 8192 | (2,.914),(2.4,1),(2.26,1) |
| 10 | 16384 | (3,1.6),(3.086,2),(3,1.74) |
| 11 | 32768 | (1.6,3),(1.74,3),(2,3.086) |

All decimal literals in this document denote exact terminating rationals.
The four residual optional auxiliary-set choices occur in domains5,6,7,10;
the listed common points are valid for every surviving ownership choice.

## Newly derived whole-row obligations

`Compact/Geometry/C898ForcedRow.lean` supplies short theorems in the unchanged
original `OpenSquare` model. They are source-assembled, awaiting the root's
serial Lean validation at the time this note was written.

1. **Domain6 contains (3,2.5) strictly.** It is an interior point of the
   actual compulsory triangle. Its exact weights on
   `(2.35,2.35),(3,2.26),(3.086,3)` are
   `(1032,15605,7800)/24437`, all positive. The source proves this using the
   already checked strict-centroid lemma and a positive linear combination.
2. **Domain8 contains (1,2.5) strictly.** Use its actual left wall, its
   closed points `(.914,2),(1,2.4)`, the excluded point `(.76,1.87)` owned by
   domain1, and the excluded point `(1.74,2)` owned by domain7. The new
   all-orientation wall theorem applies without any pose enclosure.
3. **Domain7 contains (2,2.5) strictly.** Horizontal reflection turns its
   original triangle into the proved A triangle. Domain6 supplies the
   foreign compulsory bottom point, domain8 supplies the actual wall
   neighbor, and domain5 supplies the two required missing points.
4. Thus any fourth disjoint square with a horizontal section longer than
   one at `y=2.5` is impossible: that section must contain one of the
   three already occupied points `(1,2.5),(2,2.5),(3,2.5)`.

The row theorem does not assume that any particular fourth square already
has a long section. Establishing that fact from the original geometry is
the remaining mathematical step for this candidate shortcut.

## Why the completed four-square B argument does not directly finish C898

Domain11 is a natural candidate for the fourth section, but it **owns**
`(2,3.086)`. The four-square B corner argument requires that point to be
missing. Its other compulsory point `(1.65,2.35)` belongs to domain7 here,
not domain11. Substituting domain11 into that completed B theorem would
therefore introduce false premises. Its small top triangle alone does not
force a long section at2.5.

The original geometric trace, at lines3169–3209, instead uses:

- domain1 against8; domain2 against10; domain3 against11;
- domain6 against the reduced3, then10;
- domain7 against the reduced6, then11;
- domain9 against the reduced2; domain0 against the reduced1;
- two vertical-chord pruning steps for central domain5, with neighbors
  `(0,7,11)` and `(3,6,9)`;
- four final pair refinements of domain5 against0,6,7,9.

This confirms a coupled central obstruction. Domain4, the top-left corner,
is not used at all in that original 11-square geometric replay. Its actual
closed points are a potentially useful additional input for a new direct
argument, but no valid top-row contradiction has yet been derived from
those points.

## Precisely remaining

- Replay the short new row source and connect the authenticated common
  point consequences to the exact original packing entry.
- Prove a fourth long section at2.5, or another direct incompatibility of
  the original domains; the new occupied row alone is insufficient.
- Until that final mathematical implication is proved, retain the complete
  existing C898 proof as the reference result and its compact mechanical
  translation as the fallback. Do not count this row reduction as a second
  completed proof of the case.
