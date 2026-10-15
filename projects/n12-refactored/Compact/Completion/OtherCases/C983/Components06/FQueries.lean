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

def fQueries6 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 753),
   (certified_query% 754),
   (certified_query% 755),
   (certified_query% 756),
   (certified_query% 757),
   (certified_query% 758),
   (certified_query% 759),
   N12Compact.HistoricalOwnership.Queries.query1418_certified,
   N12Compact.HistoricalOwnership.Queries.query1411_certified]

def fSignatures6 : List Signature :=
  [(1024,0,{0},{4}),
   (1024,0,{1},{3,5}),
   (1024,0,{2},{6}),
   (1024,0,{3},{5}),
   (1024,0,{4},{5,9}),
   (1024,0,{6},∅),
   (1024,0,{8},{5,9}),
   (1024,0,{1,5},{4}),
   (1024,0,{1,3},∅)]

theorem fExact6 :
    fSignatures6=fQueries6.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component06Data
