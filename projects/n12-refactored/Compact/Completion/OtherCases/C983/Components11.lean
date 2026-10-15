import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 11, mask 32768.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries11 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1536),
   (certified_query% 1537),
   (certified_query% 1539),
   (certified_query% 1545),
   (certified_query% 1554),
   (certified_query% 1566),
   (certified_query% 1575),
   (certified_query% 1544),
   (certified_query% 1552),
   (certified_query% 1553),
   (certified_query% 1560),
   (certified_query% 1565),
   (certified_query% 1558)]

private def fSignatures11 : List Signature :=
  [(32768,0,{0},∅),
   (32768,0,{1},∅),
   (32768,0,{2},{3,5}),
   (32768,0,{4},{5}),
   (32768,0,{6},{5,7}),
   (32768,0,{8},∅),
   (32768,0,{9},∅),
   (32768,0,{2,3},∅),
   (32768,0,{2,5},∅),
   (32768,0,{4,5},∅),
   (32768,0,{5,6},∅),
   (32768,0,{6,7},∅),
   (32768,0,{3,6},{5})]

private theorem fExact11 :
    fSignatures11=fQueries11.map (fun q => signature q.val) := by decide +kernel

private def fSingle11 : SingleDomain :=
  ⟨32768,1,3,[{3},{5},{7},{3,5},{3,7},{5,7},{3,5,7}],fQueries11⟩

private theorem fChecked11 :
    fSingle11.Check family 0 fSignatures11 := by decide +kernel

private def gQueries11 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1585),
   (certified_query% 1586),
   (certified_query% 1588),
   (certified_query% 1591),
   (certified_query% 1598),
   (certified_query% 1604),
   (certified_query% 1617),
   (certified_query% 1626)]

private def gSignatures11 : List Signature :=
  [(32768,1,{0},∅),
   (32768,1,{1},{4}),
   (32768,1,{2},∅),
   (32768,1,{3},∅),
   (32768,1,{5},∅),
   (32768,1,{6},∅),
   (32768,1,{8},∅),
   (32768,1,{9},{7})]

private theorem gExact11 :
    gSignatures11=gQueries11.map (fun q => signature q.val) := by decide +kernel

private def gSingle11 : SingleDomain :=
  ⟨32768,1,2,[{4},{7},{1,4},{4,7},{7,9}],gQueries11⟩

private theorem gChecked11 :
    gSingle11.Check family 1 gSignatures11 := by decide +kernel

private def rawDomain11 : CertifiedDomain family :=
  product family fSingle11 gSingle11 fSignatures11 gSignatures11
    fExact11 gExact11 fChecked11 gChecked11 (by rfl)

private def cachedProduct11 : CertifiedDomain family :=
  DomainTransport.cache rawDomain11 32768
    [{3,14},{3,17},{3,11,14},{3,14,17},{3,17,19},{5,14},{5,17},{5,11,14},{5,14,17},{5,17,19},{7,14},{7,17},{7,11,14},{7,14,17},{7,17,19},{3,5,14},{3,5,17},{3,5,11,14},{3,5,14,17},{3,5,17,19},{3,7,14},{3,7,17},{3,7,11,14},{3,7,14,17},{3,7,17,19},{5,7,14},{5,7,17},{5,7,11,14},{5,7,14,17},{5,7,17,19},{3,5,7,14},{3,5,7,17},{3,5,7,11,14},{3,5,7,14,17},{3,5,7,17,19}] (by rfl) (by decide +kernel)

private def combinedQueries11 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1644),
   (certified_query% 1635),
   (certified_query% 1645),
   (certified_query% 1636),
   (certified_query% 1639),
   (certified_query% 1650)]

private def combinedSignatures11 : List Signature :=
  [(32768,2,{3,17},{14}),
   (32768,2,{5,14},{3,7}),
   (32768,2,{5,17},{3,7}),
   (32768,2,{7,14},{17}),
   (32768,2,{5,11,14},∅),
   (32768,2,{5,17,19},∅)]

private theorem combinedExact11 :
    combinedSignatures11=combinedQueries11.map (fun q => signature q.val) := by decide +kernel

private def filtered11 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct11 combinedQueries11 combinedSignatures11 combinedExact11)

def initial11 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered11 32768
    [{3,14},{3,11,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17},{3,5,7,14,17}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

