import Compact.Completion.OtherCases.C983.RowIdentity
import Compact.Completion.OtherCases.MonotoneRefinement
import Compact.Completion.OtherCases.DomainCache
import Compact.Bridge.SharedLocalQueries


/-! Genuine full C983 auxiliary budget for original owner 0, mask 1.
Query certificates are reused symbolically under the exact owned/foreign
signature conditions. All finite cuts are ordinary kernel decisions. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

private def fQueries0 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 0),
   (certified_query% 1),
   (certified_query% 5),
   (certified_query% 9),
   (certified_query% 14),
   (certified_query% 20),
   (certified_query% 27),
   (certified_query% 35),
   (certified_query% 44),
   (certified_query% 3),
   (certified_query% 8),
   (certified_query% 12),
   (certified_query% 17),
   (certified_query% 23),
   (certified_query% 30),
   (certified_query% 38),
   (certified_query% 47)]

private def fSignatures0 : List Signature :=
  [(1,0,{0},{2}),
   (1,0,{1},{0}),
   (1,0,{3},{2}),
   (1,0,{4},{2}),
   (1,0,{5},{2}),
   (1,0,{6},{2}),
   (1,0,{7},{2}),
   (1,0,{8},{2}),
   (1,0,{9},{2}),
   (1,0,{0,2},∅),
   (1,0,{2,3},∅),
   (1,0,{2,4},∅),
   (1,0,{2,5},∅),
   (1,0,{2,6},∅),
   (1,0,{2,7},∅),
   (1,0,{2,8},∅),
   (1,0,{2,9},∅)]

private theorem fExact0 :
    fSignatures0=fQueries0.map (fun q => signature q.val) := by decide +kernel

private def fSingle0 : SingleDomain :=
  ⟨1,1,3,[{2}],fQueries0⟩

private theorem fChecked0 :
    fSingle0.Check family 0 fSignatures0 := by decide +kernel

private def gQueries0 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 54),
   (certified_query% 55),
   (certified_query% 58),
   (certified_query% 62),
   (certified_query% 67),
   (certified_query% 73),
   (certified_query% 80),
   (certified_query% 88),
   (certified_query% 97),
   (certified_query% 70),
   (certified_query% 76),
   (certified_query% 91),
   (certified_query% 100)]

private def gSignatures0 : List Signature :=
  [(1,1,{0},{2}),
   (1,1,{1},{0}),
   (1,1,{3},∅),
   (1,1,{4},∅),
   (1,1,{5},{2}),
   (1,1,{6},{2}),
   (1,1,{7},∅),
   (1,1,{8},{2}),
   (1,1,{9},{2}),
   (1,1,{2,5},∅),
   (1,1,{2,6},∅),
   (1,1,{2,8},∅),
   (1,1,{2,9},∅)]

private theorem gExact0 :
    gSignatures0=gQueries0.map (fun q => signature q.val) := by decide +kernel

private def gSingle0 : SingleDomain :=
  ⟨1,1,2,[{2},{0,2}],gQueries0⟩

private theorem gChecked0 :
    gSingle0.Check family 1 gSignatures0 := by decide +kernel

private def rawDomain0 : CertifiedDomain family :=
  product family fSingle0 gSingle0 fSignatures0 gSignatures0
    fExact0 gExact0 fChecked0 gChecked0 (by rfl)

private def cachedProduct0 : CertifiedDomain family :=
  DomainTransport.cache rawDomain0 1
    [{2,12},{2,10,12}] (by rfl) (by decide +kernel)

private def combinedQueries0 : List {q : LocalQuery // q.Check} :=
  []

private def combinedSignatures0 : List Signature :=
  []

private theorem combinedExact0 :
    combinedSignatures0=combinedQueries0.map (fun q => signature q.val) := by decide +kernel

private def filtered0 : CertifiedDomain family :=
  diameterFilter (trim cachedProduct0 combinedQueries0 combinedSignatures0 combinedExact0)

def initial0 : DomainTransport.NamedDomain family :=
  ⟨DomainTransport.cache filtered0 1
    [{2,12},{2,10,12}] (by rfl) (by decide +kernel),by decide +kernel⟩

end
end N12Compact.Completion.OtherCases.C983

