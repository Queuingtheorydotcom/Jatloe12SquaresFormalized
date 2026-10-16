# Four merged-lower cases: complete source arguments

11 October 2026. Cases **71, 80, 589 and590** now have whole-case Lean source
exclusions, including their actual original retained-row identities. **These
new files and the updated registry have not been compiled.** The earlier
58-case registry receipt does not certify the changed 62-case registry.

## Mathematical reduction

The merged lower central square does not need a pose decomposition. Keep only
nine owners' auxiliary domains; omit the lower square and the two corner-pair
owners from the finite enumeration. All twelve squares remain in the original
packing, so omitting these three domain restrictions safely enlarges the cover.

The actual F exemption count is two. Consequently each selected owner has
exactly one F point. The actual G exemption count is three, so a selected
nonexempt owner may have either one or two G points. Existing checked domain
specifications with wider cardinality bounds remain valid, and a proved filter
removes the extra F cardinalities. Horizontal reflection transports complete
owner sets, including their exact negative membership information.

The exceptional marker8196 owner in case590 has F={6}. Its original seed
triangle forces G5, but does **not** force G to be a singleton. All ten
possibilities—G={5}, or G={5,j} for j≠5—are retained.

Pairwise disjointness of the nine actual owner sets leaves fourteen complete
assignments for cases71,80,589 and eighteen for590. Only twelve distinct
four-owner bindings are needed. Every binding fits one of two arguments or
its horizontal reflection:

1. The existing coupled four-square argument: an elbow-shaped central square,
   its upper neighbor and both wall squares contradict their actual supports.
2. The unit-span argument: the upper neighbor has strict points at heights2
   and3, so at height2.5 it contains a closed unit segment entirely in its
   strict interior. The other three squares occupy (1,2.5),(2,2.5),(3,2.5).
   Any such unit segment within the container contains at least one of these
   points, contradicting disjointness.

The second argument is continuous in the orientation. Its strict section
construction handles zero sine and every angle endpoint. It needs no assumed
left corner barrier or incoming pose cover. The first argument's two corner
barriers come from genuine singleton-marker seed theorems, not archived hulls.

## Actual source chain

- `Compact/Bridge/RelaxedOwnerDomain.lean`: budget widening, exact F filter,
  full-set reflection and the exceptional seeded G domain.
- `Compact/Cases/MergedLower/Domains7180.lean` and `Domains589590.lean`:
  the nine certified original-packing domains for each family.
- `Compact/Cases/MergedLower/Recipes.lean`: the twelve bindings, with four
  geometric patterns. No angle subdivisions are stored.
- `Compact/Bridge/FourSquareVectorCover.lean`: actual pairwise-disjoint owner
  sets belong to the finite cover; each selected binding yields False in the
  original normalized packing. Geometry is checked separately from bindings
  to avoid repeating point computations through the enumeration.
- `Compact/Cases/MergedLower/Complete.lean`: the four entire-family exclusions.
- `Compact/Assembly/MergedLowerCases.lean`: original table positions110,119,
  330,331 bind the families to every retained row with IDs71,80,589,590.

`SymbolicRegistry` now has 62 source entries and55 remaining original case
contracts. Its global optimality theorem is still conditional. This is neither
a full n=12 theorem nor a claim that the new62-case source replay has passed.

## Evidence and trust

The bounded exact diagnostic `scripts/audit_merged_lower.py` reads the original
domain-specification source, exhaustively enumerates the selected owner sets,
checks every recipe's positive/negative marker and auxiliary point membership,
and locates the original rows. It completed in under0.2seconds. Its report is
`evidence/merged-lower-exact-audit.json`; it is not consumed as a trusted axiom.
Ordinary kernel checks in Lean must independently validate the actual finite
domains, recipe checks, coverage and row lookups at the final replay.

An independent source review found no missing geometric or ownership premise.
It identified and corrected two uses of the reserved keyword `section` as a
variable name. Elaboration errors may remain until the user-authorized final
whole-proof compilation.

No new native check, admission or custom axiom is introduced. The original
checked domain data and row-classification foundation retain their historical
native-certificate dependencies. Those dependencies remain visible in the
final axiom audit; this is not an ordinary-axiom-only claim.
