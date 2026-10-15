import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries
import Compact.HistoricalOwnership.Queries043

/-! Genuine full C983 auxiliary budget for original owner 3, mask 48.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries3 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query1387_certified,
   N12Compact.HistoricalOwnership.Queries.query1388_certified,
   N12Compact.HistoricalOwnership.Queries.query1389_certified,
   N12Compact.HistoricalOwnership.Queries.query1390_certified,
   N12Compact.HistoricalOwnership.Queries.query1391_certified,
   N12Compact.HistoricalOwnership.Queries.query1392_certified,
   N12Compact.HistoricalOwnership.Queries.query1393_certified,
   N12Compact.HistoricalOwnership.Queries.query1394_certified]

private def fSignatures3 : List Signature :=
  [(48,0,{0},∅),
   (48,0,{1},∅),
   (48,0,{2},∅),
   (48,0,{3},{7}),
   (48,0,{4},∅),
   (48,0,{5},∅),
   (48,0,{6},∅),
   (48,0,{8},{9})]

private theorem fExact3 :
    fSignatures3=fQueries3.map (fun q => signature q.val) := by decide +kernel

private def fSingle3 : SingleDomain :=
  ⟨48,0,2,[∅,{7},{9},{3,7},{7,9},{8,9}],fQueries3⟩

private theorem fChecked3 :
    fSingle3.Check family 0 fSignatures3 := by decide +kernel

private def gQueries3 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query1395_certified,
   N12Compact.HistoricalOwnership.Queries.query1396_certified,
   N12Compact.HistoricalOwnership.Queries.query1397_certified,
   N12Compact.HistoricalOwnership.Queries.query1398_certified,
   N12Compact.HistoricalOwnership.Queries.query1399_certified,
   N12Compact.HistoricalOwnership.Queries.query1400_certified,
   N12Compact.HistoricalOwnership.Queries.query1401_certified,
   N12Compact.HistoricalOwnership.Queries.query1402_certified]

private def gSignatures3 : List Signature :=
  [(48,1,{0},∅),
   (48,1,{1},∅),
   (48,1,{2},∅),
   (48,1,{3},∅),
   (48,1,{4},{7}),
   (48,1,{5},∅),
   (48,1,{6},∅),
   (48,1,{8},{9})]

private theorem gExact3 :
    gSignatures3=gQueries3.map (fun q => signature q.val) := by decide +kernel

private def gSingle3 : SingleDomain :=
  ⟨48,0,1,[∅,{7},{9}],gQueries3⟩

private theorem gChecked3 :
    gSingle3.Check family 1 gSignatures3 := by decide +kernel

private def rawDomain3 : CertifiedDomain family :=
  product family fSingle3 gSingle3 fSignatures3 gSignatures3
    fExact3 gExact3 fChecked3 gChecked3 (by rfl)

private def cachedProduct3 : CertifiedDomain family :=
  DomainTransport.cache rawDomain3 48
    [∅,{17},{19},{7},{7,17},{7,19},{9},{9,17},{9,19},{3,7},{3,7,17},{3,7,19},{7,9},{7,9,17},{7,9,19},{8,9},{8,9,17},{8,9,19}] (by rfl) (by decide +kernel)

private def combinedQueries3 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query1403_certified,
   N12Compact.HistoricalOwnership.Queries.query1404_certified]

private def combinedSignatures3 : List Signature :=
  [(48,2,{17},{7}),
   (48,2,{9},{19})]

private theorem combinedExact3 :
    combinedSignatures3=combinedQueries3.map (fun q => signature q.val) := by decide +kernel

private def filtered3 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct3 combinedQueries3 combinedSignatures3 combinedExact3)

def initial3 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered3 48
    [∅,{19},{7},{7,17},{7,19},{9,19},{7,9,19},{8,9,19}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

