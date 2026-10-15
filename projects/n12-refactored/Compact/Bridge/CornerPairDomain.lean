import Compact.Bridge.TransformedOwnerBudget
import S12.DomainSpecData

/-! The two corner/inner marker pairs needed by cases424,993,994.
The only domain reduction beyond symmetry is exact convexity of three
already owned points. No continuous-domain certificates are introduced. -/
namespace N12Compact.CornerPairDomain
open S12 OwnerBudget
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def mismatch520 (j : Fin 10) : LocalQuery :=
  ⟨520,2,{8,j.val+10},.hull
    ⟨(1543/500,1),(47/20,33/20),(3,87/50),(3,8/5),43/368,19285/24437⟩⟩

theorem mismatch520_checked (j : Fin 10) (hne : j.val ≠ 8) : (mismatch520 j).Check := by
  fin_cases j <;> first | exact False.elim (hne rfl) | decide +kernel

def mismatch2112 (j : Fin 10) : LocalQuery :=
  ⟨2112,2,{j.val,14},.hull
    ⟨(1,1543/500),(33/20,47/20),(87/50,3),(8/5,3),43/368,19285/24437⟩⟩

theorem mismatch2112_checked (j : Fin 10) (hne : j.val ≠ 3) : (mismatch2112 j).Check := by
  fin_cases j <;> first | exact False.elim (hne rfl) | decide +kernel

noncomputable def domain520 (family : Finset Nat)
    (hc0 : (family ∩ auxExempt 0).card = 2)
    (hc1 : (family ∩ auxExempt 1).card = 2) : CertifiedDomain family :=
  let known := HalfDomain.ofTransformedSingletonSpec family 520 0 0
    ⟨false,true,false⟩ (by decide +kernel) singleSpec24 singleSpec24_checked
    (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
    reflectXF (by decide +kernel) [{8},{6}] (by decide +kernel)
    hc0 (by decide +kernel)
  let broad := HalfDomain.singleton family 520 1 hc1 (by decide +kernel)
  let d0 := OwnerBudget.product family 520 known broad
  let d1 := (d0).remove family (mismatch520 0)
    (mismatch520_checked 0 (by decide +kernel)) (by rfl) (by rfl)
  let d2 := (d1).remove family (mismatch520 1)
    (mismatch520_checked 1 (by decide +kernel)) (by rfl) (by rfl)
  let d3 := (d2).remove family (mismatch520 2)
    (mismatch520_checked 2 (by decide +kernel)) (by rfl) (by rfl)
  let d4 := (d3).remove family (mismatch520 3)
    (mismatch520_checked 3 (by decide +kernel)) (by rfl) (by rfl)
  let d5 := (d4).remove family (mismatch520 4)
    (mismatch520_checked 4 (by decide +kernel)) (by rfl) (by rfl)
  let d6 := (d5).remove family (mismatch520 5)
    (mismatch520_checked 5 (by decide +kernel)) (by rfl) (by rfl)
  let d7 := (d6).remove family (mismatch520 6)
    (mismatch520_checked 6 (by decide +kernel)) (by rfl) (by rfl)
  let d8 := (d7).remove family (mismatch520 7)
    (mismatch520_checked 7 (by decide +kernel)) (by rfl) (by rfl)
  let d9 := (d8).remove family (mismatch520 9)
    (mismatch520_checked 9 (by decide +kernel)) (by rfl) (by rfl)
  d9

noncomputable def domain2112 (family : Finset Nat)
    (hc0 : (family ∩ auxExempt 0).card = 2)
    (hc1 : (family ∩ auxExempt 1).card = 2) : CertifiedDomain family :=
  let known := HalfDomain.ofTransformedSingletonSpec family 2112 1 0
    ⟨true,false,true⟩ (by decide +kernel) singleSpec24 singleSpec24_checked
    (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
    turnFG (by decide +kernel) [{4},{1}] (by decide +kernel)
    hc1 (by decide +kernel)
  let broad := HalfDomain.singleton family 2112 0 hc0 (by decide +kernel)
  let d0 := OwnerBudget.product family 2112 broad known
  let d1 := (d0).remove family (mismatch2112 0)
    (mismatch2112_checked 0 (by decide +kernel)) (by rfl) (by rfl)
  let d2 := (d1).remove family (mismatch2112 1)
    (mismatch2112_checked 1 (by decide +kernel)) (by rfl) (by rfl)
  let d3 := (d2).remove family (mismatch2112 2)
    (mismatch2112_checked 2 (by decide +kernel)) (by rfl) (by rfl)
  let d4 := (d3).remove family (mismatch2112 4)
    (mismatch2112_checked 4 (by decide +kernel)) (by rfl) (by rfl)
  let d5 := (d4).remove family (mismatch2112 5)
    (mismatch2112_checked 5 (by decide +kernel)) (by rfl) (by rfl)
  let d6 := (d5).remove family (mismatch2112 6)
    (mismatch2112_checked 6 (by decide +kernel)) (by rfl) (by rfl)
  let d7 := (d6).remove family (mismatch2112 7)
    (mismatch2112_checked 7 (by decide +kernel)) (by rfl) (by rfl)
  let d8 := (d7).remove family (mismatch2112 8)
    (mismatch2112_checked 8 (by decide +kernel)) (by rfl) (by rfl)
  let d9 := (d8).remove family (mismatch2112 9)
    (mismatch2112_checked 9 (by decide +kernel)) (by rfl) (by rfl)
  d9

#print axioms domain520
#print axioms domain2112
end N12Compact.CornerPairDomain
