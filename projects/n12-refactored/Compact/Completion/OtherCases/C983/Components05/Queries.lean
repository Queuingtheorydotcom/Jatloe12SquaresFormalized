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

def combinedQueries5 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 717),
   (certified_query% 676),
   (certified_query% 692),
   (certified_query% 684),
   (certified_query% 699),
   (certified_query% 720),
   (certified_query% 677),
   (certified_query% 694),
   (certified_query% 685),
   (certified_query% 700),
   (certified_query% 722),
   (certified_query% 670),
   (certified_query% 690),
   (certified_query% 705),
   (certified_query% 671),
   (certified_query% 706),
   (certified_query% 673),
   (certified_query% 708),
   (certified_query% 672),
   (certified_query% 707),
   (certified_query% 674),
   (certified_query% 709)]

def combinedSignatures5 : List Signature :=
  [(512,2,{4,16,19},{8}),
   (512,2,{6,12,15},{4}),
   (512,2,{6,12,16},{15}),
   (512,2,{6,13,15},{4}),
   (512,2,{6,13,16},{4}),
   (512,2,{6,16,19},{18}),
   (512,2,{8,12,15},{4}),
   (512,2,{8,12,16},{4,6}),
   (512,2,{8,13,15},{4}),
   (512,2,{8,13,16},{4}),
   (512,2,{8,16,19},{9}),
   (512,2,{2,4,15},{12}),
   (512,2,{2,4,16},{15}),
   (512,2,{2,4,18},{6}),
   (512,2,{4,5,15},{16}),
   (512,2,{4,5,18},{16}),
   (512,2,{4,9,15},{16,18}),
   (512,2,{4,9,18},{8}),
   (512,2,{5,8,15},{16}),
   (512,2,{5,8,18},{16}),
   (512,2,{8,9,15},{16}),
   (512,2,{8,9,18},{16})]

theorem combinedExact5 :
    combinedSignatures5=combinedQueries5.map (fun q => signature q.val) := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component05Data
