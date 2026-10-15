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

def gQueries6 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 760),
   (certified_query% 761),
   (certified_query% 762),
   (certified_query% 763),
   (certified_query% 764),
   (certified_query% 765),
   (certified_query% 766),
   N12Compact.HistoricalOwnership.Queries.query1462_certified]

def gSignatures6 : List Signature :=
  [(1024,1,{0},{1}),
   (1024,1,{1},∅),
   (1024,1,{2},{3}),
   (1024,1,{3},{6,7}),
   (1024,1,{4},{6,7}),
   (1024,1,{5},{6,8}),
   (1024,1,{8},{6}),
   (1024,1,{5,6},{3})]

theorem gExact6 :
    gSignatures6=gQueries6.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component06Data
