import Compact.Cases.C979.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined979Step1 : CertifiedDomain case979Family := domain979_0_0.refineAgainst domain979_1_0 (by decide +kernel) (by decide +kernel)
def refined979Step2 : CertifiedDomain case979Family := domain979_1_0.refineAgainst refined979Step1 (by decide +kernel) (by decide +kernel)
def refined979Step3 : CertifiedDomain case979Family := domain979_5_127.refineAgainst refined979Step1 (by decide +kernel) (by decide +kernel)
def refined979Step4 : CertifiedDomain case979Family := refined979Step3.refineAgainst refined979Step2 (by decide +kernel) (by decide +kernel)
def refined979Step5 : CertifiedDomain case979Family := refined979Step4.refineAgainst domain979_7_53 (by decide +kernel) (by decide +kernel)
def refined979Step6 : CertifiedDomain case979Family := domain979_6_127.refineAgainst refined979Step1 (by decide +kernel) (by decide +kernel)
def refined979Step7 : CertifiedDomain case979Family := refined979Step6.refineAgainst refined979Step5 (by decide +kernel) (by decide +kernel)
def refined979Step8 : CertifiedDomain case979Family := refined979Step7.refineAgainst domain979_7_53 (by decide +kernel) (by decide +kernel)
def refined979Step9 : CertifiedDomain case979Family := refined979Step8.refineAgainst domain979_10_23 (by decide +kernel) (by decide +kernel)
def refined979Step10 : CertifiedDomain case979Family := domain979_7_53.refineAgainst refined979Step2 (by decide +kernel) (by decide +kernel)
def refined979Step11 : CertifiedDomain case979Family := refined979Step10.refineAgainst refined979Step5 (by decide +kernel) (by decide +kernel)
def refined979Step12 : CertifiedDomain case979Family := refined979Step11.refineAgainst domain979_11_27 (by decide +kernel) (by decide +kernel)
def refined979Step13 : CertifiedDomain case979Family := domain979_8_23.refineAgainst refined979Step1 (by decide +kernel) (by decide +kernel)
def refined979Step14 : CertifiedDomain case979Family := refined979Step13.refineAgainst refined979Step2 (by decide +kernel) (by decide +kernel)
def refined979Step15 : CertifiedDomain case979Family := refined979Step14.refineAgainst refined979Step5 (by decide +kernel) (by decide +kernel)
def refined979Step16 : CertifiedDomain case979Family := domain979_9_27.refineAgainst refined979Step1 (by decide +kernel) (by decide +kernel)
def refined979Step17 : CertifiedDomain case979Family := refined979Step16.refineAgainst refined979Step5 (by decide +kernel) (by decide +kernel)
def refined979Step18 : CertifiedDomain case979Family := domain979_10_23.refineAgainst refined979Step9 (by decide +kernel) (by decide +kernel)
def refined979Step19 : CertifiedDomain case979Family := domain979_11_27.refineAgainst refined979Step12 (by decide +kernel) (by decide +kernel)
def refined979Step20 : CertifiedDomain case979Family := refined979Step19.refineAgainst refined979Step15 (by decide +kernel) (by decide +kernel)
def refined979Step21 : CertifiedDomain case979Family := domain979_2_5.refineAgainst refined979Step17 (by decide +kernel) (by decide +kernel)
def refined979Step22 : CertifiedDomain case979Family := domain979_4_5.refineAgainst refined979Step15 (by decide +kernel) (by decide +kernel)
def refined979Step23 : CertifiedDomain case979Family := refined979Step5.refineAgainst refined979Step15 (by decide +kernel) (by decide +kernel)
def refined979Step24 : CertifiedDomain case979Family := refined979Step23.refineAgainst refined979Step17 (by decide +kernel) (by decide +kernel)
def refined979Step25 : CertifiedDomain case979Family := refined979Step9.refineAgainst refined979Step17 (by decide +kernel) (by decide +kernel)
def refined979Step26 : CertifiedDomain case979Family := refined979Step12.refineAgainst refined979Step25 (by decide +kernel) (by decide +kernel)
def refined979Step27 : CertifiedDomain case979Family := refined979Step26.refineAgainst refined979Step15 (by decide +kernel) (by decide +kernel)
def refined979Step28 : CertifiedDomain case979Family := refined979Step18.refineAgainst refined979Step25 (by decide +kernel) (by decide +kernel)
def refined979Step29 : CertifiedDomain case979Family := refined979Step20.refineAgainst refined979Step28 (by decide +kernel) (by decide +kernel)
def refined979Step30 : CertifiedDomain case979Family := refined979Step21.refineAgainst refined979Step25 (by decide +kernel) (by decide +kernel)
def refined979Step31 : CertifiedDomain case979Family := domain979_3_5.refineAgainst refined979Step28 (by decide +kernel) (by decide +kernel)
def refined979Step32 : CertifiedDomain case979Family := refined979Step27.refineAgainst refined979Step28 (by decide +kernel) (by decide +kernel)
def case979Domain0 : CertifiedDomain case979Family := refined979Step1.enlarge [{2,12}] (by decide +kernel)
def case979Domain1 : CertifiedDomain case979Family := refined979Step2.enlarge [{0,10}] (by decide +kernel)
def case979Domain2 : CertifiedDomain case979Family := refined979Step30.enlarge [∅,{18}] (by decide +kernel)
def case979Domain3 : CertifiedDomain case979Family := refined979Step31.enlarge [∅,{7},{7,17}] (by decide +kernel)
def case979Domain4 : CertifiedDomain case979Family := refined979Step22.enlarge [∅,{3},{3,14}] (by decide +kernel)
def case979Domain5 : CertifiedDomain case979Family := refined979Step24.enlarge [{4,13},{4,13,16}] (by decide +kernel)
def case979Domain6 : CertifiedDomain case979Family := refined979Step25.enlarge [{8,16},{8,18},{8,16,18}] (by decide +kernel)
def case979Domain7 : CertifiedDomain case979Family := refined979Step32.enlarge [{5},{5,14},{5,16},{5,14,16},{5,17},{5,14,17},{5,16,17},{3,5},{3,5,14},{3,5,16},{3,5,14,16},{3,5,14,17},{5,7},{5,7,16},{5,7,17},{5,7,14,17},{5,7,16,17}] (by decide +kernel)
def case979Domain8 : CertifiedDomain case979Family := refined979Step15.enlarge [{1,11},{1,3,11}] (by decide +kernel)
def case979Domain9 : CertifiedDomain case979Family := refined979Step17.enlarge [{6,15},{6,15,18}] (by decide +kernel)
def case979Domain10 : CertifiedDomain case979Family := refined979Step28.enlarge [{9,19},{9,16,19},{7,9,19}] (by decide +kernel)
def case979Domain11 : CertifiedDomain case979Family := refined979Step29.enlarge [{3,14},{3,14,17},{7,17},{7,14,17},{3,7,14,17}] (by decide +kernel)

end
end S12
