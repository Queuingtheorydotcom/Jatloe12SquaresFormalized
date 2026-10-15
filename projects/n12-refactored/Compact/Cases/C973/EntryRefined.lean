import Compact.Cases.C973.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined973Step1 : CertifiedDomain case973Family := domain973_0_0.refineAgainst domain973_1_0 (by decide +kernel) (by decide +kernel)
def refined973Step2 : CertifiedDomain case973Family := domain973_1_0.refineAgainst refined973Step1 (by decide +kernel) (by decide +kernel)
def refined973Step3 : CertifiedDomain case973Family := domain973_5_57.refineAgainst refined973Step1 (by decide +kernel) (by decide +kernel)
def refined973Step4 : CertifiedDomain case973Family := refined973Step3.refineAgainst refined973Step2 (by decide +kernel) (by decide +kernel)
def refined973Step5 : CertifiedDomain case973Family := domain973_6_57.refineAgainst refined973Step1 (by decide +kernel) (by decide +kernel)
def refined973Step6 : CertifiedDomain case973Family := refined973Step5.refineAgainst refined973Step4 (by decide +kernel) (by decide +kernel)
def refined973Step7 : CertifiedDomain case973Family := refined973Step6.refineAgainst domain973_10_19 (by decide +kernel) (by decide +kernel)
def refined973Step8 : CertifiedDomain case973Family := domain973_7_57.refineAgainst refined973Step4 (by decide +kernel) (by decide +kernel)
def refined973Step9 : CertifiedDomain case973Family := refined973Step8.refineAgainst domain973_10_19 (by decide +kernel) (by decide +kernel)
def refined973Step10 : CertifiedDomain case973Family := refined973Step9.refineAgainst domain973_11_19 (by decide +kernel) (by decide +kernel)
def refined973Step11 : CertifiedDomain case973Family := domain973_8_57.refineAgainst refined973Step2 (by decide +kernel) (by decide +kernel)
def refined973Step12 : CertifiedDomain case973Family := refined973Step11.refineAgainst refined973Step4 (by decide +kernel) (by decide +kernel)
def refined973Step13 : CertifiedDomain case973Family := refined973Step12.refineAgainst domain973_11_19 (by decide +kernel) (by decide +kernel)
def refined973Step14 : CertifiedDomain case973Family := domain973_9_19.refineAgainst refined973Step1 (by decide +kernel) (by decide +kernel)
def refined973Step15 : CertifiedDomain case973Family := refined973Step14.refineAgainst refined973Step2 (by decide +kernel) (by decide +kernel)
def refined973Step16 : CertifiedDomain case973Family := refined973Step15.refineAgainst refined973Step4 (by decide +kernel) (by decide +kernel)
def refined973Step17 : CertifiedDomain case973Family := domain973_10_19.refineAgainst refined973Step7 (by decide +kernel) (by decide +kernel)
def refined973Step18 : CertifiedDomain case973Family := domain973_11_19.refineAgainst refined973Step13 (by decide +kernel) (by decide +kernel)
def refined973Step19 : CertifiedDomain case973Family := domain973_4_3.refineAgainst refined973Step16 (by decide +kernel) (by decide +kernel)
def refined973Step20 : CertifiedDomain case973Family := refined973Step4.refineAgainst refined973Step16 (by decide +kernel) (by decide +kernel)
def refined973Step21 : CertifiedDomain case973Family := refined973Step13.refineAgainst refined973Step16 (by decide +kernel) (by decide +kernel)
def refined973Step22 : CertifiedDomain case973Family := refined973Step18.refineAgainst refined973Step21 (by decide +kernel) (by decide +kernel)
def refined973Step23 : CertifiedDomain case973Family := domain973_3_3.refineAgainst refined973Step22 (by decide +kernel) (by decide +kernel)
def refined973Step24 : CertifiedDomain case973Family := refined973Step19.refineAgainst refined973Step21 (by decide +kernel) (by decide +kernel)
def refined973Step25 : CertifiedDomain case973Family := refined973Step10.refineAgainst refined973Step21 (by decide +kernel) (by decide +kernel)
def refined973Step26 : CertifiedDomain case973Family := refined973Step25.refineAgainst refined973Step22 (by decide +kernel) (by decide +kernel)
def refined973Step27 : CertifiedDomain case973Family := refined973Step17.refineAgainst refined973Step26 (by decide +kernel) (by decide +kernel)
def refined973Step28 : CertifiedDomain case973Family := refined973Step27.refineAgainst refined973Step22 (by decide +kernel) (by decide +kernel)
def case973Domain0 : CertifiedDomain case973Family := refined973Step1.enlarge [{2,12}] (by decide +kernel)
def case973Domain1 : CertifiedDomain case973Family := refined973Step2.enlarge [{0,10}] (by decide +kernel)
def case973Domain2 : CertifiedDomain case973Family := domain973_2_3.enlarge [∅,{18},{6},{6,15},{6,18},{8,18}] (by decide +kernel)
def case973Domain3 : CertifiedDomain case973Family := refined973Step23.enlarge [∅,{19},{9,19}] (by decide +kernel)
def case973Domain4 : CertifiedDomain case973Family := refined973Step24.enlarge [∅,{3}] (by decide +kernel)
def case973Domain5 : CertifiedDomain case973Family := refined973Step20.enlarge [{4,13},{4,13,15},{4,13,16},{4,5,13},{4,5,13,15},{4,5,13,16}] (by decide +kernel)
def case973Domain6 : CertifiedDomain case973Family := refined973Step7.enlarge [{6,15},{6,16},{6,15,16},{6,18},{6,15,18},{6,16,18},{8,15},{8,16},{8,15,16},{8,18},{8,15,18},{8,16,18},{5,8,16},{5,8,15,16},{5,8,16,18},{6,8,15},{6,8,16},{6,8,15,16},{6,8,18},{6,8,15,18},{6,8,16,18},{8,9,16},{8,9,15,16},{8,9,16,18},{8,9,16,19}] (by decide +kernel)
def case973Domain7 : CertifiedDomain case973Family := refined973Step26.enlarge [{5,16},{5,19},{5,16,19},{5,8,16},{9,16},{9,19},{9,16,19},{5,9,16},{5,9,19},{5,9,16,19},{8,9,16},{8,9,16,18},{8,9,16,19}] (by decide +kernel)
def case973Domain8 : CertifiedDomain case973Family := refined973Step21.enlarge [{3,14},{5,14},{5,14,16},{3,5,14},{3,5,14,16}] (by decide +kernel)
def case973Domain9 : CertifiedDomain case973Family := refined973Step16.enlarge [{1,11},{1,3,11}] (by decide +kernel)
def case973Domain10 : CertifiedDomain case973Family := refined973Step28.enlarge [{8,18},{8,16,18},{6,8,18},{9,19},{9,16,19},{8,9,18},{8,9,16,18},{8,9,19},{8,9,16,19},{8,9,18,19}] (by decide +kernel)
def case973Domain11 : CertifiedDomain case973Family := refined973Step22.enlarge [{7,17},{7,17,19},{5,7,17}] (by decide +kernel)

end
end S12
