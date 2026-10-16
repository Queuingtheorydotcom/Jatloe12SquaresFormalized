# Shared historical entrance queries

`scripts/compact_historical_queries.py` prepares an isolated replacement for
the five historical entrance proposals. It preserves every original query
value and its original consumer, including both single-owner query collections
and later `CertifiedDomain.remove` filters. Unknown consumer syntax rejects the
entire proposal; a failed producer removes its own staging directory.

The completed proposal records 7,102 original query uses: 5,980 entries in
owner query lists and 1,122 domain filters. Direct canonical selection removes
3,900 local aliases. Interning the remaining 3,202 source expressions leaves
2,193 distinct new query records. The complete five-entrance source decreases
from 49,759 to 32,946 lines, a measured saving of 16,813 lines. Exact input and
output hashes are in
`evidence/proposals/HistoricalInitialSharedQueries/manifest.json`.

`SharedLocalQueries.select` uses the existing canonical chunk theorem; it
does not manufacture a new arithmetic proof. The original `LocalQueryData`
chunk theorems retain their inherited `native_decide` trust boundary.
`checked_local_query` emits an ordinary named proof for each new record with
`decide +kernel`; there is no new native checker. The query helper and new
records still require replay, particularly rational hull checks. This source
sharing does not establish any complete historical case by itself.
