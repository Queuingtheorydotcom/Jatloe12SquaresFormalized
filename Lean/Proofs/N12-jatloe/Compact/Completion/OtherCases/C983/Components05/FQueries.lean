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

def fQueries5 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 582),
   (certified_query% 583),
   (certified_query% 585),
   (certified_query% 588),
   (certified_query% 595),
   (certified_query% 605),
   (certified_query% 618),
   (certified_query% 592),
   (certified_query% 586),
   (certified_query% 594),
   (certified_query% 603)]

def fSignatures5 : List Signature :=
  [(512,0,{0},{2,4}),
   (512,0,{1},{5}),
   (512,0,{2},{4}),
   (512,0,{3},{7}),
   (512,0,{5},{4,8}),
   (512,0,{7},∅),
   (512,0,{9},{4,8}),
   (512,0,{0,4},{5}),
   (512,0,{0,2},∅),
   (512,0,{3,4},{5}),
   (512,0,{3,6},{5})]

theorem fExact5 :
    fSignatures5=fQueries5.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component05Data
