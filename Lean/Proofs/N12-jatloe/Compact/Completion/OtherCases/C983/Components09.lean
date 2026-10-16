import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 9, mask 8192.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries9 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1145),
   (certified_query% 1146),
   (certified_query% 1150),
   (certified_query% 1157),
   (certified_query% 1167),
   (certified_query% 1175),
   (certified_query% 1184),
   (certified_query% 1153),
   (certified_query% 1156),
   (certified_query% 1162),
   (certified_query% 1172),
   (certified_query% 1174),
   (certified_query% 1170)]

private def fSignatures9 : List Signature :=
  [(8192,0,{0},∅),
   (8192,0,{1},∅),
   (8192,0,{3},{2,4}),
   (8192,0,{5},{4}),
   (8192,0,{7},{4,6}),
   (8192,0,{8},∅),
   (8192,0,{9},∅),
   (8192,0,{2,3},∅),
   (8192,0,{3,4},∅),
   (8192,0,{4,5},∅),
   (8192,0,{4,7},∅),
   (8192,0,{6,7},∅),
   (8192,0,{2,7},{4})]

private theorem fExact9 :
    fSignatures9=fQueries9.map (fun q => signature q.val) := by decide +kernel

private def fSingle9 : SingleDomain :=
  ⟨8192,1,3,[{2},{4},{6},{2,4},{2,6},{4,6},{2,4,6}],fQueries9⟩

private theorem fChecked9 :
    fSingle9.Check family 0 fSignatures9 := by decide +kernel

private def gQueries9 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1194),
   (certified_query% 1195),
   (certified_query% 1198),
   (certified_query% 1202),
   (certified_query% 1211),
   (certified_query% 1218),
   (certified_query% 1226),
   (certified_query% 1234)]

private def gSignatures9 : List Signature :=
  [(8192,1,{0},{2}),
   (8192,1,{1},∅),
   (8192,1,{3},∅),
   (8192,1,{4},∅),
   (8192,1,{6},∅),
   (8192,1,{7},∅),
   (8192,1,{8},{5}),
   (8192,1,{9},∅)]

private theorem gExact9 :
    gSignatures9=gQueries9.map (fun q => signature q.val) := by decide +kernel

private def gSingle9 : SingleDomain :=
  ⟨8192,1,2,[{2},{5},{0,2},{2,5},{5,8}],gQueries9⟩

private theorem gChecked9 :
    gSingle9.Check family 1 gSignatures9 := by decide +kernel

private def rawDomain9 : CertifiedDomain family :=
  product family fSingle9 gSingle9 fSignatures9 gSignatures9
    fExact9 gExact9 fChecked9 gChecked9 (by rfl)

private def cachedProduct9 : CertifiedDomain family :=
  DomainTransport.cache rawDomain9 8192
    [{2,12},{2,15},{2,10,12},{2,12,15},{2,15,18},{4,12},{4,15},{4,10,12},{4,12,15},{4,15,18},{6,12},{6,15},{6,10,12},{6,12,15},{6,15,18},{2,4,12},{2,4,15},{2,4,10,12},{2,4,12,15},{2,4,15,18},{2,6,12},{2,6,15},{2,6,10,12},{2,6,12,15},{2,6,15,18},{4,6,12},{4,6,15},{4,6,10,12},{4,6,12,15},{4,6,15,18},{2,4,6,12},{2,4,6,15},{2,4,6,10,12},{2,4,6,12,15},{2,4,6,15,18}] (by rfl) (by decide +kernel)

private def combinedQueries9 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1253),
   (certified_query% 1244),
   (certified_query% 1254),
   (certified_query% 1245),
   (certified_query% 1248),
   (certified_query% 1259)]

private def combinedSignatures9 : List Signature :=
  [(8192,2,{2,15},{12}),
   (8192,2,{4,12},{2,6}),
   (8192,2,{4,15},{2,6}),
   (8192,2,{6,12},{15}),
   (8192,2,{4,10,12},∅),
   (8192,2,{4,15,18},∅)]

private theorem combinedExact9 :
    combinedSignatures9=combinedQueries9.map (fun q => signature q.val) := by decide +kernel

private def filtered9 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct9 combinedQueries9 combinedSignatures9 combinedExact9)

def initial9 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered9 8192
    [{2,12},{2,10,12},{2,12,15},{6,15},{6,12,15},{6,15,18},{2,4,12},{2,4,12,15},{2,6,12,15},{4,6,15},{4,6,12,15},{2,4,6,12,15}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

