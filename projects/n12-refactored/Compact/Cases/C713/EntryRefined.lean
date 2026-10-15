import Compact.Cases.C713.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined713Step1 : CertifiedDomain case713Family := domain713_1_0.refineAgainst domain713_0_0 (by decide +kernel) (by decide +kernel)
def refined713Step2 : CertifiedDomain case713Family := domain713_4_0.refineAgainst domain713_3_0 (by decide +kernel) (by decide +kernel)
def refined713Step3 : CertifiedDomain case713Family := domain713_6_11.refineAgainst refined713Step2 (by decide +kernel) (by decide +kernel)
def refined713Step4 : CertifiedDomain case713Family := domain713_7_0.refineAgainst domain713_0_0 (by decide +kernel) (by decide +kernel)
def refined713Step5 : CertifiedDomain case713Family := refined713Step4.refineAgainst refined713Step1 (by decide +kernel) (by decide +kernel)
def refined713Step6 : CertifiedDomain case713Family := domain713_8_9.refineAgainst domain713_0_0 (by decide +kernel) (by decide +kernel)
def refined713Step7 : CertifiedDomain case713Family := refined713Step6.refineAgainst refined713Step1 (by decide +kernel) (by decide +kernel)
def refined713Step8 : CertifiedDomain case713Family := domain713_9_8.refineAgainst domain713_0_0 (by decide +kernel) (by decide +kernel)
def refined713Step9 : CertifiedDomain case713Family := domain713_10_9.refineAgainst domain713_3_0 (by decide +kernel) (by decide +kernel)
def refined713Step10 : CertifiedDomain case713Family := refined713Step9.refineAgainst refined713Step2 (by decide +kernel) (by decide +kernel)
def refined713Step11 : CertifiedDomain case713Family := refined713Step10.refineAgainst refined713Step8 (by decide +kernel) (by decide +kernel)
def refined713Step12 : CertifiedDomain case713Family := domain713_11_8.refineAgainst domain713_3_0 (by decide +kernel) (by decide +kernel)
def refined713Step13 : CertifiedDomain case713Family := domain713_2_1.refineAgainst refined713Step8 (by decide +kernel) (by decide +kernel)
def refined713Step14 : CertifiedDomain case713Family := domain713_5_1.refineAgainst refined713Step12 (by decide +kernel) (by decide +kernel)
def refined713Step15 : CertifiedDomain case713Family := refined713Step3.refineAgainst refined713Step8 (by decide +kernel) (by decide +kernel)
def refined713Step16 : CertifiedDomain case713Family := refined713Step15.refineAgainst refined713Step11 (by decide +kernel) (by decide +kernel)
def refined713Step17 : CertifiedDomain case713Family := refined713Step5.refineAgainst refined713Step16 (by decide +kernel) (by decide +kernel)
def refined713Step18 : CertifiedDomain case713Family := refined713Step17.refineAgainst refined713Step7 (by decide +kernel) (by decide +kernel)
def refined713Step19 : CertifiedDomain case713Family := refined713Step18.refineAgainst refined713Step12 (by decide +kernel) (by decide +kernel)
def refined713Step20 : CertifiedDomain case713Family := refined713Step7.refineAgainst refined713Step12 (by decide +kernel) (by decide +kernel)
def refined713Step21 : CertifiedDomain case713Family := refined713Step8.refineAgainst refined713Step16 (by decide +kernel) (by decide +kernel)
def case713Domain0 : CertifiedDomain case713Family := domain713_0_0.enlarge [{2,12}] (by decide +kernel)
def case713Domain1 : CertifiedDomain case713Family := refined713Step1.enlarge [{0,10}] (by decide +kernel)
def case713Domain2 : CertifiedDomain case713Family := refined713Step13.enlarge [∅] (by decide +kernel)
def case713Domain3 : CertifiedDomain case713Family := domain713_3_0.enlarge [{7,17}] (by decide +kernel)
def case713Domain4 : CertifiedDomain case713Family := refined713Step2.enlarge [{9,19}] (by decide +kernel)
def case713Domain5 : CertifiedDomain case713Family := refined713Step14.enlarge [∅] (by decide +kernel)
def case713Domain6 : CertifiedDomain case713Family := refined713Step16.enlarge [{4,16},{4,5,16}] (by decide +kernel)
def case713Domain7 : CertifiedDomain case713Family := refined713Step19.enlarge [{13},{5,13}] (by decide +kernel)
def case713Domain8 : CertifiedDomain case713Family := refined713Step20.enlarge [{1,11}] (by decide +kernel)
def case713Domain9 : CertifiedDomain case713Family := refined713Step21.enlarge [{6,15}] (by decide +kernel)
def case713Domain10 : CertifiedDomain case713Family := refined713Step11.enlarge [{8,18}] (by decide +kernel)
def case713Domain11 : CertifiedDomain case713Family := refined713Step12.enlarge [{3,14},{3,5,14}] (by decide +kernel)

end
end S12
