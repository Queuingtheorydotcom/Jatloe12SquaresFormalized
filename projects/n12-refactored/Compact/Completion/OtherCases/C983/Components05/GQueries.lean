import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component05Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def gQueries5 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 626),
   (certified_query% 627),
   (certified_query% 629),
   (certified_query% 632),
   (certified_query% 636),
   (certified_query% 647),
   (certified_query% 661),
   (certified_query% 654)]

def gSignatures5 : List Signature :=
  [(512,1,{0},∅),
   (512,1,{1},{0}),
   (512,1,{2},{5,6}),
   (512,1,{3},{5,6}),
   (512,1,{4},{3}),
   (512,1,{7},{6,9}),
   (512,1,{9},{6}),
   (512,1,{6,7},{3})]

theorem gExact5 :
    gSignatures5=gQueries5.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component05Data
