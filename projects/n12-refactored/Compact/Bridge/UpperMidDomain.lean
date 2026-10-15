import Compact.Bridge.TransformedOwnerBudget
import S12.DomainSpecData

/-! The top-middle/inner marker pair is the half-turn of the already
proved bottom-middle pair. A second auxiliary point is forced by one exact
triangle whenever F3 is owned, excluding that singleton assignment. -/
namespace N12Compact.UpperMidDomain
open S12 OwnerBudget
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable def halfTurnF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![9,8,7,6,5,4,3,2,1,0] (by decide +kernel)

def mismatch33792 (j : Fin 10) : LocalQuery :=
  ⟨33792,2,{3,j.val+10},.hull
    ⟨(8/5,3),(2,1543/500),(47/20,47/20),(87/50,3),
      4550/15623,602/16225⟩⟩

theorem mismatch33792_checked (j : Fin 10) (hne : j.val ≠ 4) :
    (mismatch33792 j).Check := by
  fin_cases j <;> first | exact False.elim (hne rfl) | decide +kernel

noncomputable def domain33792 (family : Finset Nat)
    (hc0 : (family ∩ auxExempt 0).card = 2)
    (hc1 : (family ∩ auxExempt 1).card = 2) : CertifiedDomain family :=
  let first := HalfDomain.ofTransformedSingletonSpec family 33792 0 0
    ⟨false,true,true⟩ (by decide +kernel) singleSpec72 singleSpec72_checked
    (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
    halfTurnF (by decide +kernel) [{7},{5},{3}] (by decide +kernel)
    hc0 (by decide +kernel)
  let second := HalfDomain.ofSpec family singleSpec101 1 singleSpec101_checked
    (by
      refine ⟨rfl, by decide +kernel, ?_⟩
      change 1 = (family ∩ auxExempt 1).card - 2 + 1
      rw [hc1])
  let d0 := OwnerBudget.product family 33792 first second
  let d1 := CertifiedDomain.remove family d0 (mismatch33792 6)
    (mismatch33792_checked 6 (by decide +kernel)) (by rfl) (by rfl)
  let d2 := CertifiedDomain.remove family d1 (mismatch33792 7)
    (mismatch33792_checked 7 (by decide +kernel)) (by rfl) (by rfl)
  CertifiedDomain.remove family d2 (mismatch33792 9)
    (mismatch33792_checked 9 (by decide +kernel)) (by rfl) (by rfl)

#print axioms domain33792
end N12Compact.UpperMidDomain
