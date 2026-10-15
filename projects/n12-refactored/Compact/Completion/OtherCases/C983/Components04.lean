import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries
import Compact.HistoricalOwnership.Queries001
import Compact.HistoricalOwnership.Queries024
import Compact.HistoricalOwnership.Queries025

/-! Genuine full C983 auxiliary budget for original owner 4, mask 192.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries4 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query53_certified,
   N12Compact.HistoricalOwnership.Queries.query54_certified,
   N12Compact.HistoricalOwnership.Queries.query55_certified,
   N12Compact.HistoricalOwnership.Queries.query56_certified,
   N12Compact.HistoricalOwnership.Queries.query57_certified,
   N12Compact.HistoricalOwnership.Queries.query58_certified,
   N12Compact.HistoricalOwnership.Queries.query59_certified,
   N12Compact.HistoricalOwnership.Queries.query60_certified]

private def fSignatures4 : List Signature :=
  [(192,0,{0},{1}),
   (192,0,{2},∅),
   (192,0,{4},∅),
   (192,0,{5},∅),
   (192,0,{6},∅),
   (192,0,{7},{3}),
   (192,0,{8},∅),
   (192,0,{9},∅)]

private theorem fExact4 :
    fSignatures4=fQueries4.map (fun q => signature q.val) := by decide +kernel

private def fSingle4 : SingleDomain :=
  ⟨192,0,2,[∅,{1},{3},{0,1},{1,3},{3,7}],fQueries4⟩

private theorem fChecked4 :
    fSingle4.Check family 0 fSignatures4 := by decide +kernel

private def gQueries4 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query769_certified,
   N12Compact.HistoricalOwnership.Queries.query771_certified,
   N12Compact.HistoricalOwnership.Queries.query774_certified,
   N12Compact.HistoricalOwnership.Queries.query781_certified,
   N12Compact.HistoricalOwnership.Queries.query787_certified,
   N12Compact.HistoricalOwnership.Queries.query794_certified,
   N12Compact.HistoricalOwnership.Queries.query802_certified,
   N12Compact.HistoricalOwnership.Queries.query811_certified]

private def gSignatures4 : List Signature :=
  [(192,1,{0},{1}),
   (192,1,{2},∅),
   (192,1,{3},∅),
   (192,1,{5},∅),
   (192,1,{6},∅),
   (192,1,{7},{4}),
   (192,1,{8},∅),
   (192,1,{9},∅)]

private theorem gExact4 :
    gSignatures4=gQueries4.map (fun q => signature q.val) := by decide +kernel

private def gSingle4 : SingleDomain :=
  ⟨192,0,1,[∅,{1},{4}],gQueries4⟩

private theorem gChecked4 :
    gSingle4.Check family 1 gSignatures4 := by decide +kernel

private def rawDomain4 : CertifiedDomain family :=
  product family fSingle4 gSingle4 fSignatures4 gSignatures4
    fExact4 gExact4 fChecked4 gChecked4 (by rfl)

private def cachedProduct4 : CertifiedDomain family :=
  DomainTransport.cache rawDomain4 192
    [∅,{11},{14},{1},{1,11},{1,14},{3},{3,11},{3,14},{0,1},{0,1,11},{0,1,14},{1,3},{1,3,11},{1,3,14},{3,7},{3,7,11},{3,7,14}] (by rfl) (by decide +kernel)

private def combinedQueries4 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query821_certified,
   N12Compact.HistoricalOwnership.Queries.query61_certified]

private def combinedSignatures4 : List Signature :=
  [(192,2,{14},{3}),
   (192,2,{1},{11})]

private theorem combinedExact4 :
    combinedSignatures4=combinedQueries4.map (fun q => signature q.val) := by decide +kernel

private def filtered4 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct4 combinedQueries4 combinedSignatures4 combinedExact4)

def initial4 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered4 192
    [∅,{11},{1,11},{3},{3,11},{3,14},{0,1,11},{1,3,11}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

