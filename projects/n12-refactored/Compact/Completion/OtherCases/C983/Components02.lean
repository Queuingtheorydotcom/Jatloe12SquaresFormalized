import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries
import Compact.HistoricalOwnership.Queries000
import Compact.HistoricalOwnership.Queries012
import Compact.HistoricalOwnership.Queries013

/-! Genuine full C983 auxiliary budget for original owner 2, mask 12.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries2 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query0_certified,
   N12Compact.HistoricalOwnership.Queries.query1_certified,
   N12Compact.HistoricalOwnership.Queries.query2_certified,
   N12Compact.HistoricalOwnership.Queries.query3_certified,
   N12Compact.HistoricalOwnership.Queries.query4_certified,
   N12Compact.HistoricalOwnership.Queries.query5_certified,
   N12Compact.HistoricalOwnership.Queries.query6_certified,
   N12Compact.HistoricalOwnership.Queries.query7_certified]

private def fSignatures2 : List Signature :=
  [(12,0,{0},∅),
   (12,0,{1},∅),
   (12,0,{2},{6}),
   (12,0,{3},∅),
   (12,0,{4},∅),
   (12,0,{5},∅),
   (12,0,{7},∅),
   (12,0,{9},{8})]

private theorem fExact2 :
    fSignatures2=fQueries2.map (fun q => signature q.val) := by decide +kernel

private def fSingle2 : SingleDomain :=
  ⟨12,0,2,[∅,{6},{8},{2,6},{6,8},{8,9}],fQueries2⟩

private theorem fChecked2 :
    fSingle2.Check family 0 fSignatures2 := by decide +kernel

private def gQueries2 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query386_certified,
   N12Compact.HistoricalOwnership.Queries.query387_certified,
   N12Compact.HistoricalOwnership.Queries.query389_certified,
   N12Compact.HistoricalOwnership.Queries.query392_certified,
   N12Compact.HistoricalOwnership.Queries.query396_certified,
   N12Compact.HistoricalOwnership.Queries.query406_certified,
   N12Compact.HistoricalOwnership.Queries.query413_certified,
   N12Compact.HistoricalOwnership.Queries.query428_certified]

private def gSignatures2 : List Signature :=
  [(12,1,{0},∅),
   (12,1,{1},∅),
   (12,1,{2},{5}),
   (12,1,{3},∅),
   (12,1,{4},∅),
   (12,1,{6},∅),
   (12,1,{7},∅),
   (12,1,{9},{8})]

private theorem gExact2 :
    gSignatures2=gQueries2.map (fun q => signature q.val) := by decide +kernel

private def gSingle2 : SingleDomain :=
  ⟨12,0,1,[∅,{5},{8}],gQueries2⟩

private theorem gChecked2 :
    gSingle2.Check family 1 gSignatures2 := by decide +kernel

private def rawDomain2 : CertifiedDomain family :=
  product family fSingle2 gSingle2 fSignatures2 gSignatures2
    fExact2 gExact2 fChecked2 gChecked2 (by rfl)

private def cachedProduct2 : CertifiedDomain family :=
  DomainTransport.cache rawDomain2 12
    [∅,{15},{18},{6},{6,15},{6,18},{8},{8,15},{8,18},{2,6},{2,6,15},{2,6,18},{6,8},{6,8,15},{6,8,18},{8,9},{8,9,15},{8,9,18}] (by rfl) (by decide +kernel)

private def combinedQueries2 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query438_certified,
   N12Compact.HistoricalOwnership.Queries.query8_certified]

private def combinedSignatures2 : List Signature :=
  [(12,2,{15},{6}),
   (12,2,{8},{18})]

private theorem combinedExact2 :
    combinedSignatures2=combinedQueries2.map (fun q => signature q.val) := by decide +kernel

private def filtered2 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct2 combinedQueries2 combinedSignatures2 combinedExact2)

def initial2 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered2 12
    [∅,{18},{6},{6,15},{6,18},{8,18},{6,8,18},{8,9,18}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

