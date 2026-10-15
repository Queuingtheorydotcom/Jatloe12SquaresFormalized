import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 1, mask 2.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries1 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 107),
   (certified_query% 109),
   (certified_query% 111),
   (certified_query% 115),
   (certified_query% 120),
   (certified_query% 126),
   (certified_query% 133),
   (certified_query% 141),
   (certified_query% 150),
   (certified_query% 116),
   (certified_query% 121),
   (certified_query% 127),
   (certified_query% 134),
   (certified_query% 142),
   (certified_query% 151)]

private def fSignatures1 : List Signature :=
  [(2,0,{1},∅),
   (2,0,{2},{0}),
   (2,0,{3},∅),
   (2,0,{4},{0}),
   (2,0,{5},{0}),
   (2,0,{6},{0}),
   (2,0,{7},{0}),
   (2,0,{8},{0}),
   (2,0,{9},{0}),
   (2,0,{0,4},∅),
   (2,0,{0,5},∅),
   (2,0,{0,6},{2}),
   (2,0,{0,7},∅),
   (2,0,{0,8},∅),
   (2,0,{0,9},∅)]

private theorem fExact1 :
    fSignatures1=fQueries1.map (fun q => signature q.val) := by decide +kernel

private def fSingle1 : SingleDomain :=
  ⟨2,1,3,[{0},{0,2},{0,2,6}],fQueries1⟩

private theorem fChecked1 :
    fSingle1.Check family 0 fSignatures1 := by decide +kernel

private def gQueries1 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 160),
   (certified_query% 162),
   (certified_query% 165),
   (certified_query% 169),
   (certified_query% 174),
   (certified_query% 180),
   (certified_query% 187),
   (certified_query% 195),
   (certified_query% 204),
   (certified_query% 163),
   (certified_query% 166),
   (certified_query% 175),
   (certified_query% 181),
   (certified_query% 188),
   (certified_query% 196),
   (certified_query% 205)]

private def gSignatures1 : List Signature :=
  [(2,1,{1},∅),
   (2,1,{2},{0}),
   (2,1,{3},{0}),
   (2,1,{4},∅),
   (2,1,{5},{0}),
   (2,1,{6},{0}),
   (2,1,{7},{0}),
   (2,1,{8},{0}),
   (2,1,{9},{0}),
   (2,1,{0,2},∅),
   (2,1,{0,3},∅),
   (2,1,{0,5},{2}),
   (2,1,{0,6},∅),
   (2,1,{0,7},∅),
   (2,1,{0,8},∅),
   (2,1,{0,9},∅)]

private theorem gExact1 :
    gSignatures1=gQueries1.map (fun q => signature q.val) := by decide +kernel

private def gSingle1 : SingleDomain :=
  ⟨2,1,2,[{0}],gQueries1⟩

private theorem gChecked1 :
    gSingle1.Check family 1 gSignatures1 := by decide +kernel

private def rawDomain1 : CertifiedDomain family :=
  product family fSingle1 gSingle1 fSignatures1 gSignatures1
    fExact1 gExact1 fChecked1 gChecked1 (by rfl)

private def cachedProduct1 : CertifiedDomain family :=
  DomainTransport.cache rawDomain1 2
    [{0,10},{0,2,10},{0,2,6,10}] (by rfl) (by decide +kernel)

private def combinedQueries1 : List {q : LocalQuery // q.Check} :=
  []

private def combinedSignatures1 : List Signature :=
  []

private theorem combinedExact1 :
    combinedSignatures1=combinedQueries1.map (fun q => signature q.val) := by decide +kernel

private def filtered1 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct1 combinedQueries1 combinedSignatures1 combinedExact1)

def initial1 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered1 2
    [{0,10},{0,2,10}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

