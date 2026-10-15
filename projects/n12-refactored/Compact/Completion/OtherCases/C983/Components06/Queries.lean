import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries
import Compact.HistoricalOwnership.Queries044
import Compact.HistoricalOwnership.Queries045
import Compact.HistoricalOwnership.Queries046
import Compact.HistoricalOwnership.Queries047
import Compact.HistoricalOwnership.Queries048

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component06Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def combinedQueries6 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query1481_certified,
   N12Compact.HistoricalOwnership.Queries.query1498_certified,
   N12Compact.HistoricalOwnership.Queries.query1500_certified,
   N12Compact.HistoricalOwnership.Queries.query1499_certified,
   N12Compact.HistoricalOwnership.Queries.query1501_certified,
   N12Compact.HistoricalOwnership.Queries.query1502_certified,
   N12Compact.HistoricalOwnership.Queries.query1512_certified,
   N12Compact.HistoricalOwnership.Queries.query1514_certified,
   N12Compact.HistoricalOwnership.Queries.query1513_certified,
   N12Compact.HistoricalOwnership.Queries.query1515_certified,
   N12Compact.HistoricalOwnership.Queries.query1516_certified,
   N12Compact.HistoricalOwnership.Queries.query1482_certified,
   N12Compact.HistoricalOwnership.Queries.query1485_certified,
   N12Compact.HistoricalOwnership.Queries.query1489_certified,
   N12Compact.HistoricalOwnership.Queries.query1492_certified,
   N12Compact.HistoricalOwnership.Queries.query1496_certified,
   N12Compact.HistoricalOwnership.Queries.query1519_certified,
   N12Compact.HistoricalOwnership.Queries.query1523_certified,
   N12Compact.HistoricalOwnership.Queries.query1505_certified,
   N12Compact.HistoricalOwnership.Queries.query1509_certified,
   N12Compact.HistoricalOwnership.Queries.query1533_certified,
   N12Compact.HistoricalOwnership.Queries.query1536_certified]

def combinedSignatures6 : List Signature :=
  [(1024,2,{5,16,18},{9}),
   (1024,2,{7,13,16},{5}),
   (1024,2,{7,13,17},{5}),
   (1024,2,{7,14,16},{17}),
   (1024,2,{7,14,17},{5}),
   (1024,2,{7,16,18},{19}),
   (1024,2,{9,13,16},{5}),
   (1024,2,{9,13,17},{5}),
   (1024,2,{9,14,16},{5,7}),
   (1024,2,{9,14,17},{5}),
   (1024,2,{9,16,18},{8}),
   (1024,2,{3,5,16},{17}),
   (1024,2,{3,5,17},{14}),
   (1024,2,{3,5,19},{7}),
   (1024,2,{4,5,17},{16}),
   (1024,2,{4,5,19},{16}),
   (1024,2,{4,9,17},{16}),
   (1024,2,{4,9,19},{16}),
   (1024,2,{5,8,17},{16,19}),
   (1024,2,{5,8,19},{9}),
   (1024,2,{8,9,17},{16}),
   (1024,2,{8,9,19},{16})]

theorem combinedExact6 :
    combinedSignatures6=combinedQueries6.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component06Data
