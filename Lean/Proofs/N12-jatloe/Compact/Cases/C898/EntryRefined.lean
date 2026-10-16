import Compact.Cases.C898.EntryDomains
import S12.DomainRefinement

namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def refined898Step1 : CertifiedDomain case898Family := domain898_0_0.refineAgainst domain898_1_0 (by decide +kernel) (by decide +kernel)
def refined898Step2 : CertifiedDomain case898Family := domain898_3_0.refineAgainst domain898_6_7 (by decide +kernel) (by decide +kernel)
def refined898Step3 : CertifiedDomain case898Family := domain898_5_0.refineAgainst refined898Step1 (by decide +kernel) (by decide +kernel)
def refined898Step4 : CertifiedDomain case898Family := refined898Step3.refineAgainst domain898_1_0 (by decide +kernel) (by decide +kernel)
def refined898Step5 : CertifiedDomain case898Family := domain898_6_7.refineAgainst refined898Step2 (by decide +kernel) (by decide +kernel)
def refined898Step6 : CertifiedDomain case898Family := domain898_7_11.refineAgainst refined898Step2 (by decide +kernel) (by decide +kernel)
def refined898Step7 : CertifiedDomain case898Family := domain898_8_8.refineAgainst domain898_1_0 (by decide +kernel) (by decide +kernel)
def refined898Step8 : CertifiedDomain case898Family := domain898_9_9.refineAgainst refined898Step1 (by decide +kernel) (by decide +kernel)
def refined898Step9 : CertifiedDomain case898Family := domain898_10_8.refineAgainst refined898Step5 (by decide +kernel) (by decide +kernel)
def refined898Step10 : CertifiedDomain case898Family := domain898_11_9.refineAgainst refined898Step2 (by decide +kernel) (by decide +kernel)
def refined898Step11 : CertifiedDomain case898Family := refined898Step10.refineAgainst refined898Step7 (by decide +kernel) (by decide +kernel)
def refined898Step12 : CertifiedDomain case898Family := domain898_2_1.refineAgainst refined898Step9 (by decide +kernel) (by decide +kernel)
def refined898Step13 : CertifiedDomain case898Family := domain898_4_1.refineAgainst refined898Step7 (by decide +kernel) (by decide +kernel)
def refined898Step14 : CertifiedDomain case898Family := refined898Step4.refineAgainst refined898Step8 (by decide +kernel) (by decide +kernel)
def refined898Step15 : CertifiedDomain case898Family := refined898Step14.refineAgainst refined898Step9 (by decide +kernel) (by decide +kernel)
def refined898Step16 : CertifiedDomain case898Family := refined898Step6.refineAgainst refined898Step7 (by decide +kernel) (by decide +kernel)
def refined898Step17 : CertifiedDomain case898Family := refined898Step16.refineAgainst refined898Step11 (by decide +kernel) (by decide +kernel)
def refined898Step18 : CertifiedDomain case898Family := refined898Step7.refineAgainst refined898Step17 (by decide +kernel) (by decide +kernel)
def refined898Step19 : CertifiedDomain case898Family := refined898Step8.refineAgainst refined898Step9 (by decide +kernel) (by decide +kernel)
def refined898Step20 : CertifiedDomain case898Family := refined898Step15.refineAgainst refined898Step17 (by decide +kernel) (by decide +kernel)
def case898Domain0 : CertifiedDomain case898Family := refined898Step1.enlarge [{2,12}] (by decide +kernel)
def case898Domain1 : CertifiedDomain case898Family := domain898_1_0.enlarge [{0,10}] (by decide +kernel)
def case898Domain2 : CertifiedDomain case898Family := refined898Step12.enlarge [∅] (by decide +kernel)
def case898Domain3 : CertifiedDomain case898Family := refined898Step2.enlarge [{7,17}] (by decide +kernel)
def case898Domain4 : CertifiedDomain case898Family := refined898Step13.enlarge [∅] (by decide +kernel)
def case898Domain5 : CertifiedDomain case898Family := refined898Step20.enlarge [{4},{4,16}] (by decide +kernel)
def case898Domain6 : CertifiedDomain case898Family := refined898Step5.enlarge [{9,19},{9,16,19}] (by decide +kernel)
def case898Domain7 : CertifiedDomain case898Family := refined898Step17.enlarge [{5,13},{5,13,16}] (by decide +kernel)
def case898Domain8 : CertifiedDomain case898Family := refined898Step18.enlarge [{1,11}] (by decide +kernel)
def case898Domain9 : CertifiedDomain case898Family := refined898Step19.enlarge [{6,15}] (by decide +kernel)
def case898Domain10 : CertifiedDomain case898Family := refined898Step9.enlarge [{8,18},{8,16,18}] (by decide +kernel)
def case898Domain11 : CertifiedDomain case898Family := refined898Step11.enlarge [{3,14}] (by decide +kernel)
def case898RefinedDomains : Fin 12 → CertifiedDomain case898Family := ![case898Domain0,case898Domain1,case898Domain2,case898Domain3,case898Domain4,case898Domain5,case898Domain6,case898Domain7,case898Domain8,case898Domain9,case898Domain10,case898Domain11]
theorem case898RefinedDomains_member : ∀ i,(case898RefinedDomains i).mask∈case898Family := by decide +kernel
end S12
