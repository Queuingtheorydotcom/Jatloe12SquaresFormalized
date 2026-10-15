import Compact.Completion.OtherCases.C715.MergedQueries
import Compact.Completion.OtherCases.DomainCache
import Compact.Cases.C713.EntryQueries

/-! Genuine auxiliary entrance for original C715. Eleven unchanged owner
masks reuse local refutations from C713, with the F and G budgets checked
again against the actual C715 family. The merged mask 17408 has its own
exact geometric refutations. Two complete domain refinements retain every
actual owner subset, including all possible two-point F ownership. -/

namespace N12Compact.Completion.OtherCases.C715
open S12 S12Pilot
open N12Compact.Completion.OtherCases.DomainTransport
set_option Elab.async false
noncomputable section

def domain715_0_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_0_0 single713_0_1
    (rebase single713_0_0 case713Family family 0 single713_0_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_0_1 case713Family family 1 single713_0_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_1_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_1_0 single713_1_1
    (rebase single713_1_0 case713Family family 0 single713_1_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_1_1 case713Family family 1 single713_1_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_2_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_2_0 single713_2_1
    (rebase single713_2_0 case713Family family 0 single713_2_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_2_1 case713Family family 1 single713_2_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_2_1 : CertifiedDomain family := .remove _ domain715_2_0 query713_133 query713_133_checked (by decide +kernel) (by decide +kernel)

def domain715_3_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_3_0 single713_3_1
    (rebase single713_3_0 case713Family family 0 single713_3_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_3_1 case713Family family 1 single713_3_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_4_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_4_0 single713_4_1
    (rebase single713_4_0 case713Family family 0 single713_4_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_4_1 case713Family family 1 single713_4_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_5_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_5_0 single713_5_1
    (rebase single713_5_0 case713Family family 0 single713_5_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_5_1 case713Family family 1 single713_5_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_5_1 : CertifiedDomain family := .remove _ domain715_5_0 query713_267 query713_267_checked (by decide +kernel) (by decide +kernel)

def domain715_6_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_6_0 single713_6_1
    (rebase single713_6_0 case713Family family 0 single713_6_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_6_1 case713Family family 1 single713_6_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_6_1 : CertifiedDomain family := .remove _ domain715_6_0 query713_319 query713_319_checked (by decide +kernel) (by decide +kernel)

def domain715_6_2 : CertifiedDomain family := .remove _ domain715_6_1 query713_320 query713_320_checked (by decide +kernel) (by decide +kernel)

def domain715_6_3 : CertifiedDomain family := .remove _ domain715_6_2 query713_321 query713_321_checked (by decide +kernel) (by decide +kernel)

def domain715_6_4 : CertifiedDomain family := .remove _ domain715_6_3 query713_322 query713_322_checked (by decide +kernel) (by decide +kernel)

def domain715_6_5 : CertifiedDomain family := .remove _ domain715_6_4 query713_323 query713_323_checked (by decide +kernel) (by decide +kernel)

def domain715_6_6 : CertifiedDomain family := .remove _ domain715_6_5 query713_324 query713_324_checked (by decide +kernel) (by decide +kernel)

def domain715_6_7 : CertifiedDomain family := .remove _ domain715_6_6 query713_325 query713_325_checked (by decide +kernel) (by decide +kernel)

def domain715_6_8 : CertifiedDomain family := .remove _ domain715_6_7 query713_326 query713_326_checked (by decide +kernel) (by decide +kernel)

def domain715_6_9 : CertifiedDomain family := .remove _ domain715_6_8 query713_327 query713_327_checked (by decide +kernel) (by decide +kernel)

def domain715_6_10 : CertifiedDomain family := .remove _ domain715_6_9 query713_328 query713_328_checked (by decide +kernel) (by decide +kernel)

def domain715_6_11 : CertifiedDomain family := .remove _ domain715_6_10 query713_329 query713_329_checked (by decide +kernel) (by decide +kernel)

def domain715_7_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_7_0 single713_7_1
    (rebase single713_7_0 case713Family family 0 single713_7_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_7_1 case713Family family 1 single713_7_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_8_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_8_0 single713_8_1
    (rebase single713_8_0 case713Family family 0 single713_8_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_8_1 case713Family family 1 single713_8_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_8_1 : CertifiedDomain family := .remove _ domain715_8_0 query713_400 query713_400_checked (by decide +kernel) (by decide +kernel)

def domain715_8_2 : CertifiedDomain family := .remove _ domain715_8_1 query713_401 query713_401_checked (by decide +kernel) (by decide +kernel)

def domain715_8_3 : CertifiedDomain family := .remove _ domain715_8_2 query713_402 query713_402_checked (by decide +kernel) (by decide +kernel)

def domain715_8_4 : CertifiedDomain family := .remove _ domain715_8_3 query713_403 query713_403_checked (by decide +kernel) (by decide +kernel)

def domain715_8_5 : CertifiedDomain family := .remove _ domain715_8_4 query713_404 query713_404_checked (by decide +kernel) (by decide +kernel)

def domain715_8_6 : CertifiedDomain family := .remove _ domain715_8_5 query713_405 query713_405_checked (by decide +kernel) (by decide +kernel)

def domain715_8_7 : CertifiedDomain family := .remove _ domain715_8_6 query713_406 query713_406_checked (by decide +kernel) (by decide +kernel)

def domain715_8_8 : CertifiedDomain family := .remove _ domain715_8_7 query713_407 query713_407_checked (by decide +kernel) (by decide +kernel)

def domain715_8_9 : CertifiedDomain family := .remove _ domain715_8_8 query713_408 query713_408_checked (by decide +kernel) (by decide +kernel)

def domain715_9_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_9_0 single713_9_1
    (rebase single713_9_0 case713Family family 0 single713_9_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_9_1 case713Family family 1 single713_9_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_9_1 : CertifiedDomain family := .remove _ domain715_9_0 query713_466 query713_466_checked (by decide +kernel) (by decide +kernel)

def domain715_9_2 : CertifiedDomain family := .remove _ domain715_9_1 query713_467 query713_467_checked (by decide +kernel) (by decide +kernel)

def domain715_9_3 : CertifiedDomain family := .remove _ domain715_9_2 query713_468 query713_468_checked (by decide +kernel) (by decide +kernel)

def domain715_9_4 : CertifiedDomain family := .remove _ domain715_9_3 query713_469 query713_469_checked (by decide +kernel) (by decide +kernel)

def domain715_9_5 : CertifiedDomain family := .remove _ domain715_9_4 query713_470 query713_470_checked (by decide +kernel) (by decide +kernel)

def domain715_9_6 : CertifiedDomain family := .remove _ domain715_9_5 query713_471 query713_471_checked (by decide +kernel) (by decide +kernel)

def domain715_9_7 : CertifiedDomain family := .remove _ domain715_9_6 query713_472 query713_472_checked (by decide +kernel) (by decide +kernel)

def domain715_9_8 : CertifiedDomain family := .remove _ domain715_9_7 query713_473 query713_473_checked (by decide +kernel) (by decide +kernel)

def domain715_11_0 : CertifiedDomain family :=
  .ofDirectProduct _ single713_11_0 single713_11_1
    (rebase single713_11_0 case713Family family 0 single713_11_0_checked
      (by decide +kernel) (by decide +kernel))
    (rebase single713_11_1 case713Family family 1 single713_11_1_checked
      (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

def domain715_11_1 : CertifiedDomain family := .remove _ domain715_11_0 query713_597 query713_597_checked (by decide +kernel) (by decide +kernel)

def domain715_11_2 : CertifiedDomain family := .remove _ domain715_11_1 query713_598 query713_598_checked (by decide +kernel) (by decide +kernel)

def domain715_11_3 : CertifiedDomain family := .remove _ domain715_11_2 query713_599 query713_599_checked (by decide +kernel) (by decide +kernel)

def domain715_11_4 : CertifiedDomain family := .remove _ domain715_11_3 query713_600 query713_600_checked (by decide +kernel) (by decide +kernel)

def domain715_11_5 : CertifiedDomain family := .remove _ domain715_11_4 query713_601 query713_601_checked (by decide +kernel) (by decide +kernel)

def domain715_11_6 : CertifiedDomain family := .remove _ domain715_11_5 query713_602 query713_602_checked (by decide +kernel) (by decide +kernel)

def domain715_11_7 : CertifiedDomain family := .remove _ domain715_11_6 query713_603 query713_603_checked (by decide +kernel) (by decide +kernel)

def domain715_11_8 : CertifiedDomain family := .remove _ domain715_11_7 query713_604 query713_604_checked (by decide +kernel) (by decide +kernel)

def domain715_10_0 : CertifiedDomain family :=
  .ofDirectProduct _ mergedF mergedG mergedF_checked mergedG_checked (by decide +kernel)


def initial0 : NamedDomain family :=
  ⟨cache domain715_0_0 1 [{2,12}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial1 : NamedDomain family :=
  ⟨cache domain715_1_0 2 [{0,10},{0,2,10}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial2 : NamedDomain family :=
  ⟨cache domain715_2_1 12 [∅,{6}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial3 : NamedDomain family :=
  ⟨cache domain715_3_0 16 [{7,17}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial4 : NamedDomain family :=
  ⟨cache domain715_4_0 32 [{9,19},{7,9,19}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial5 : NamedDomain family :=
  ⟨cache domain715_5_1 192 [∅,{3}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial6 : NamedDomain family :=
  ⟨cache domain715_6_11 512 [{4,15},{4,16},{4,18},{4,5,16},{6,15},{6,16},{6,18},{4,6,15},{4,6,16},{4,6,18},{8,15},{8,16},{8,18},{4,8,15},{4,8,16},{4,8,18},{5,8,16},{6,8,15},{6,8,16},{6,8,18},{4,9,16},{8,9,16}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial7 : NamedDomain family :=
  ⟨cache domain715_7_0 2304 [{13},{0,13},{1,13},{2,13},{3,13},{4,13},{5,13}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial8 : NamedDomain family :=
  ⟨cache domain715_8_9 4096 [{0,10},{1,11},{0,1,10},{0,1,11},{0,2,10},{1,3,11}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial9 : NamedDomain family :=
  ⟨cache domain715_9_8 8192 [{2,12},{2,4,12},{6,15},{4,6,15}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial10 : NamedDomain family :=
  ⟨cache domain715_10_0 17408 [{5,16},{5,18},{5,19},{7,16},{7,18},{7,19},{9,16},{9,18},{9,19},{4,5,16},{4,5,18},{4,5,19},{4,9,16},{4,9,18},{4,9,19},{5,7,16},{5,7,18},{5,7,19},{5,8,16},{5,8,18},{5,8,19},{5,9,16},{5,9,18},{5,9,19},{7,9,16},{7,9,18},{7,9,19},{8,9,16},{8,9,18},{8,9,19}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initial11 : NamedDomain family :=
  ⟨cache domain715_11_8 32768 [{3,14},{3,5,14},{7,17},{5,7,17}]
    (by decide +kernel) (by decide +kernel),by decide +kernel⟩

def initialNamed : List (NamedDomain family) :=
  [initial0,initial1,initial2,initial3,initial4,initial5,initial6,initial7,initial8,initial9,initial10,initial11]

end
end N12Compact.Completion.OtherCases.C715
