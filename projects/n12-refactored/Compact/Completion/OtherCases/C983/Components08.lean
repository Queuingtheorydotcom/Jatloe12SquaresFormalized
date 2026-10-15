import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 8, mask 4096.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries8 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 989),
   (certified_query% 991),
   (certified_query% 994),
   (certified_query% 999),
   (certified_query% 1005),
   (certified_query% 1012),
   (certified_query% 1020),
   (certified_query% 1029)]

private def fSignatures8 : List Signature :=
  [(4096,0,{2},{0}),
   (4096,0,{3},{1}),
   (4096,0,{4},∅),
   (4096,0,{5},∅),
   (4096,0,{6},∅),
   (4096,0,{7},∅),
   (4096,0,{8},∅),
   (4096,0,{9},∅)]

private theorem fExact8 :
    fSignatures8=fQueries8.map (fun q => signature q.val) := by decide +kernel

private def fSingle8 : SingleDomain :=
  ⟨4096,1,3,[{0},{1},{0,1},{0,2},{1,3},{0,1,2},{0,1,3}],fQueries8⟩

private theorem fChecked8 :
    fSingle8.Check family 0 fSignatures8 := by decide +kernel

private def gQueries8 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1039),
   (certified_query% 1043),
   (certified_query% 1048),
   (certified_query% 1054),
   (certified_query% 1061),
   (certified_query% 1069),
   (certified_query% 1078),
   (certified_query% 1070),
   (certified_query% 1080),
   (certified_query% 1058),
   (certified_query% 1073),
   (certified_query% 1082)]

private def gSignatures8 : List Signature :=
  [(4096,1,{2},∅),
   (4096,1,{4},∅),
   (4096,1,{5},∅),
   (4096,1,{6},{3}),
   (4096,1,{7},∅),
   (4096,1,{8},{0,3}),
   (4096,1,{9},{1,3}),
   (4096,1,{0,8},∅),
   (4096,1,{1,9},∅),
   (4096,1,{3,6},∅),
   (4096,1,{3,8},∅),
   (4096,1,{3,9},∅)]

private theorem gExact8 :
    gSignatures8=gQueries8.map (fun q => signature q.val) := by decide +kernel

private def gSingle8 : SingleDomain :=
  ⟨4096,1,2,[{0},{1},{3},{0,1},{0,3},{1,3}],gQueries8⟩

private theorem gChecked8 :
    gSingle8.Check family 1 gSignatures8 := by decide +kernel

private def rawDomain8 : CertifiedDomain family :=
  product family fSingle8 gSingle8 fSignatures8 gSignatures8
    fExact8 gExact8 fChecked8 gChecked8 (by rfl)

private def cachedProduct8 : CertifiedDomain family :=
  DomainTransport.cache rawDomain8 4096
    [{0,10},{0,11},{0,13},{0,10,11},{0,10,13},{0,11,13},{1,10},{1,11},{1,13},{1,10,11},{1,10,13},{1,11,13},{0,1,10},{0,1,11},{0,1,13},{0,1,10,11},{0,1,10,13},{0,1,11,13},{0,2,10},{0,2,11},{0,2,13},{0,2,10,11},{0,2,10,13},{0,2,11,13},{1,3,10},{1,3,11},{1,3,13},{1,3,10,11},{1,3,10,13},{1,3,11,13},{0,1,2,10},{0,1,2,11},{0,1,2,13},{0,1,2,10,11},{0,1,2,10,13},{0,1,2,11,13},{0,1,3,10},{0,1,3,11},{0,1,3,13},{0,1,3,10,11},{0,1,3,10,13},{0,1,3,11,13}] (by rfl) (by decide +kernel)

private def combinedQueries8 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1090),
   (certified_query% 1096),
   (certified_query% 1088),
   (certified_query% 1097),
   (certified_query% 1099),
   (certified_query% 1100)]

private def combinedSignatures8 : List Signature :=
  [(4096,2,{0,11},{1}),
   (4096,2,{0,13},{10,11}),
   (4096,2,{1,10},{0}),
   (4096,2,{1,13},{10,11}),
   (4096,2,{0,2,13},∅),
   (4096,2,{1,3,13},∅)]

private theorem combinedExact8 :
    combinedSignatures8=combinedQueries8.map (fun q => signature q.val) := by decide +kernel

private def filtered8 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct8 combinedQueries8 combinedSignatures8 combinedExact8)

def initial8 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered8 4096
    [{0,10},{0,10,13},{1,11},{1,11,13},{0,1,10},{0,1,11},{0,1,10,11},{0,1,10,13},{0,1,11,13},{0,2,10},{1,3,11},{0,1,2,10},{0,1,3,11}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

