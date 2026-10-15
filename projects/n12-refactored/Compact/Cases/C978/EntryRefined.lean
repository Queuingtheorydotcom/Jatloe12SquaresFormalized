import Compact.Cases.C978.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined978Step1 : CertifiedDomain case978Family := domain978_0_0.refineAgainst domain978_1_0 (by decide +kernel) (by decide +kernel)
def refined978Step2 : CertifiedDomain case978Family := domain978_1_0.refineAgainst refined978Step1 (by decide +kernel) (by decide +kernel)
def refined978Step3 : CertifiedDomain case978Family := domain978_5_57.refineAgainst refined978Step1 (by decide +kernel) (by decide +kernel)
def refined978Step4 : CertifiedDomain case978Family := refined978Step3.refineAgainst refined978Step2 (by decide +kernel) (by decide +kernel)
def refined978Step5 : CertifiedDomain case978Family := domain978_6_57.refineAgainst refined978Step1 (by decide +kernel) (by decide +kernel)
def refined978Step6 : CertifiedDomain case978Family := refined978Step5.refineAgainst refined978Step4 (by decide +kernel) (by decide +kernel)
def refined978Step7 : CertifiedDomain case978Family := refined978Step6.refineAgainst domain978_10_19 (by decide +kernel) (by decide +kernel)
def refined978Step8 : CertifiedDomain case978Family := domain978_7_57.refineAgainst refined978Step2 (by decide +kernel) (by decide +kernel)
def refined978Step9 : CertifiedDomain case978Family := refined978Step8.refineAgainst refined978Step4 (by decide +kernel) (by decide +kernel)
def refined978Step10 : CertifiedDomain case978Family := refined978Step9.refineAgainst domain978_11_61 (by decide +kernel) (by decide +kernel)
def refined978Step11 : CertifiedDomain case978Family := domain978_8_19.refineAgainst refined978Step1 (by decide +kernel) (by decide +kernel)
def refined978Step12 : CertifiedDomain case978Family := refined978Step11.refineAgainst refined978Step2 (by decide +kernel) (by decide +kernel)
def refined978Step13 : CertifiedDomain case978Family := refined978Step12.refineAgainst refined978Step4 (by decide +kernel) (by decide +kernel)
def refined978Step14 : CertifiedDomain case978Family := domain978_9_19.refineAgainst refined978Step1 (by decide +kernel) (by decide +kernel)
def refined978Step15 : CertifiedDomain case978Family := refined978Step14.refineAgainst refined978Step4 (by decide +kernel) (by decide +kernel)
def refined978Step16 : CertifiedDomain case978Family := domain978_10_19.refineAgainst refined978Step7 (by decide +kernel) (by decide +kernel)
def refined978Step17 : CertifiedDomain case978Family := domain978_11_61.refineAgainst refined978Step4 (by decide +kernel) (by decide +kernel)
def refined978Step18 : CertifiedDomain case978Family := domain978_2_3.refineAgainst refined978Step15 (by decide +kernel) (by decide +kernel)
def refined978Step19 : CertifiedDomain case978Family := domain978_4_3.refineAgainst refined978Step13 (by decide +kernel) (by decide +kernel)
def refined978Step20 : CertifiedDomain case978Family := refined978Step4.refineAgainst refined978Step13 (by decide +kernel) (by decide +kernel)
def refined978Step21 : CertifiedDomain case978Family := refined978Step20.refineAgainst refined978Step15 (by decide +kernel) (by decide +kernel)
def refined978Step22 : CertifiedDomain case978Family := refined978Step7.refineAgainst refined978Step15 (by decide +kernel) (by decide +kernel)
def refined978Step23 : CertifiedDomain case978Family := refined978Step10.refineAgainst refined978Step13 (by decide +kernel) (by decide +kernel)
def refined978Step24 : CertifiedDomain case978Family := refined978Step16.refineAgainst refined978Step22 (by decide +kernel) (by decide +kernel)
def refined978Step25 : CertifiedDomain case978Family := refined978Step17.refineAgainst refined978Step22 (by decide +kernel) (by decide +kernel)
def refined978Step26 : CertifiedDomain case978Family := refined978Step25.refineAgainst refined978Step23 (by decide +kernel) (by decide +kernel)
def refined978Step27 : CertifiedDomain case978Family := refined978Step26.refineAgainst refined978Step24 (by decide +kernel) (by decide +kernel)
def refined978Step28 : CertifiedDomain case978Family := refined978Step18.refineAgainst refined978Step22 (by decide +kernel) (by decide +kernel)
def refined978Step29 : CertifiedDomain case978Family := domain978_3_3.refineAgainst refined978Step24 (by decide +kernel) (by decide +kernel)
def refined978Step30 : CertifiedDomain case978Family := refined978Step19.refineAgainst refined978Step23 (by decide +kernel) (by decide +kernel)
def case978Domain0 : CertifiedDomain case978Family := refined978Step1.enlarge [{2,12}] (by decide +kernel)
def case978Domain1 : CertifiedDomain case978Family := refined978Step2.enlarge [{0,10}] (by decide +kernel)
def case978Domain2 : CertifiedDomain case978Family := refined978Step28.enlarge [∅,{18}] (by decide +kernel)
def case978Domain3 : CertifiedDomain case978Family := refined978Step29.enlarge [∅,{7},{7,17}] (by decide +kernel)
def case978Domain4 : CertifiedDomain case978Family := refined978Step30.enlarge [∅,{3}] (by decide +kernel)
def case978Domain5 : CertifiedDomain case978Family := refined978Step21.enlarge [{4,13},{4,13,16},{4,5,13},{4,5,13,16}] (by decide +kernel)
def case978Domain6 : CertifiedDomain case978Family := refined978Step22.enlarge [{8,16},{8,18},{8,16,18},{5,8,16},{5,8,16,18}] (by decide +kernel)
def case978Domain7 : CertifiedDomain case978Family := refined978Step23.enlarge [{3,14},{5,14},{5,14,16},{5,14,17},{3,5,14},{3,5,14,16},{3,5,14,17},{5,7,14,17}] (by decide +kernel)
def case978Domain8 : CertifiedDomain case978Family := refined978Step13.enlarge [{1,11},{1,3,11}] (by decide +kernel)
def case978Domain9 : CertifiedDomain case978Family := refined978Step15.enlarge [{6,15},{6,15,18}] (by decide +kernel)
def case978Domain10 : CertifiedDomain case978Family := refined978Step24.enlarge [{9,19},{9,16,19},{7,9,19}] (by decide +kernel)
def case978Domain11 : CertifiedDomain case978Family := refined978Step27.enlarge [{5,16},{5,17},{5,16,17},{7,17},{7,16,17},{5,7,17},{5,7,16,17}] (by decide +kernel)

end
end S12
