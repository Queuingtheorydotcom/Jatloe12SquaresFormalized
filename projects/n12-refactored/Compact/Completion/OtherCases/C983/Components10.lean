import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 10, mask 16384.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries10 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1294),
   (certified_query% 1295),
   (certified_query% 1297),
   (certified_query% 1300),
   (certified_query% 1304),
   (certified_query% 1309),
   (certified_query% 1315),
   (certified_query% 1322)]

private def fSignatures10 : List Signature :=
  [(16384,0,{0},∅),
   (16384,0,{1},∅),
   (16384,0,{2},∅),
   (16384,0,{3},∅),
   (16384,0,{4},∅),
   (16384,0,{5},∅),
   (16384,0,{6},{8}),
   (16384,0,{7},{9})]

private theorem fExact10 :
    fSignatures10=fQueries10.map (fun q => signature q.val) := by decide +kernel

private def fSingle10 : SingleDomain :=
  ⟨16384,1,3,[{8},{9},{6,8},{7,9},{8,9},{6,8,9},{7,8,9}],fQueries10⟩

private theorem fChecked10 :
    fSingle10.Check family 0 fSignatures10 := by decide +kernel

private def gQueries10 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1344),
   (certified_query% 1345),
   (certified_query% 1347),
   (certified_query% 1350),
   (certified_query% 1354),
   (certified_query% 1359),
   (certified_query% 1371),
   (certified_query% 1365),
   (certified_query% 1379),
   (certified_query% 1366),
   (certified_query% 1387),
   (certified_query% 1368)]

private def gSignatures10 : List Signature :=
  [(16384,1,{0},{6,8}),
   (16384,1,{1},{6,9}),
   (16384,1,{2},∅),
   (16384,1,{3},{6}),
   (16384,1,{4},∅),
   (16384,1,{5},∅),
   (16384,1,{7},∅),
   (16384,1,{0,6},∅),
   (16384,1,{0,8},∅),
   (16384,1,{1,6},∅),
   (16384,1,{1,9},∅),
   (16384,1,{3,6},∅)]

private theorem gExact10 :
    gSignatures10=gQueries10.map (fun q => signature q.val) := by decide +kernel

private def gSingle10 : SingleDomain :=
  ⟨16384,1,2,[{6},{8},{9},{6,8},{6,9},{8,9}],gQueries10⟩

private theorem gChecked10 :
    gSingle10.Check family 1 gSignatures10 := by decide +kernel

private def rawDomain10 : CertifiedDomain family :=
  product family fSingle10 gSingle10 fSignatures10 gSignatures10
    fExact10 gExact10 fChecked10 gChecked10 (by rfl)

private def cachedProduct10 : CertifiedDomain family :=
  DomainTransport.cache rawDomain10 16384
    [{8,16},{8,18},{8,19},{8,16,18},{8,16,19},{8,18,19},{9,16},{9,18},{9,19},{9,16,18},{9,16,19},{9,18,19},{6,8,16},{6,8,18},{6,8,19},{6,8,16,18},{6,8,16,19},{6,8,18,19},{7,9,16},{7,9,18},{7,9,19},{7,9,16,18},{7,9,16,19},{7,9,18,19},{8,9,16},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19},{6,8,9,16},{6,8,9,18},{6,8,9,19},{6,8,9,16,18},{6,8,9,16,19},{6,8,9,18,19},{7,8,9,16},{7,8,9,18},{7,8,9,19},{7,8,9,16,18},{7,8,9,16,19},{7,8,9,18,19}] (by rfl) (by decide +kernel)

private def combinedQueries10 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1393),
   (certified_query% 1403),
   (certified_query% 1395),
   (certified_query% 1398),
   (certified_query% 1394),
   (certified_query% 1396)]

private def combinedSignatures10 : List Signature :=
  [(16384,2,{8,16},{18,19}),
   (16384,2,{8,19},{9}),
   (16384,2,{9,16},{18,19}),
   (16384,2,{9,18},{8}),
   (16384,2,{6,8,16},∅),
   (16384,2,{7,9,16},∅)]

private theorem combinedExact10 :
    combinedSignatures10=combinedQueries10.map (fun q => signature q.val) := by decide +kernel

private def filtered10 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct10 combinedQueries10 combinedSignatures10 combinedExact10)

def initial10 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered10 16384
    [{8,18},{8,16,18},{9,19},{9,16,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19},{6,8,9,18},{7,8,9,19}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

