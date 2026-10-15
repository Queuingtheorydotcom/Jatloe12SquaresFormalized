import Compact.Cases.C701.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined701Step1 : CertifiedDomain case701Family := domain701_1_0.refineAgainst domain701_0_0 (by decide +kernel) (by decide +kernel)
def refined701Step2 : CertifiedDomain case701Family := domain701_4_0.refineAgainst domain701_3_0 (by decide +kernel) (by decide +kernel)
def refined701Step3 : CertifiedDomain case701Family := domain701_6_11.refineAgainst domain701_0_0 (by decide +kernel) (by decide +kernel)
def refined701Step4 : CertifiedDomain case701Family := refined701Step3.refineAgainst refined701Step1 (by decide +kernel) (by decide +kernel)
def refined701Step5 : CertifiedDomain case701Family := domain701_7_0.refineAgainst domain701_3_0 (by decide +kernel) (by decide +kernel)
def refined701Step6 : CertifiedDomain case701Family := refined701Step5.refineAgainst refined701Step2 (by decide +kernel) (by decide +kernel)
def refined701Step7 : CertifiedDomain case701Family := refined701Step6.refineAgainst refined701Step4 (by decide +kernel) (by decide +kernel)
def refined701Step8 : CertifiedDomain case701Family := domain701_8_9.refineAgainst domain701_0_0 (by decide +kernel) (by decide +kernel)
def refined701Step9 : CertifiedDomain case701Family := refined701Step8.refineAgainst refined701Step1 (by decide +kernel) (by decide +kernel)
def refined701Step10 : CertifiedDomain case701Family := domain701_9_8.refineAgainst domain701_0_0 (by decide +kernel) (by decide +kernel)
def refined701Step11 : CertifiedDomain case701Family := refined701Step10.refineAgainst refined701Step4 (by decide +kernel) (by decide +kernel)
def refined701Step12 : CertifiedDomain case701Family := domain701_10_9.refineAgainst domain701_3_0 (by decide +kernel) (by decide +kernel)
def refined701Step13 : CertifiedDomain case701Family := refined701Step12.refineAgainst refined701Step2 (by decide +kernel) (by decide +kernel)
def refined701Step14 : CertifiedDomain case701Family := refined701Step13.refineAgainst refined701Step11 (by decide +kernel) (by decide +kernel)
def refined701Step15 : CertifiedDomain case701Family := domain701_11_19.refineAgainst refined701Step1 (by decide +kernel) (by decide +kernel)
def refined701Step16 : CertifiedDomain case701Family := refined701Step15.refineAgainst refined701Step4 (by decide +kernel) (by decide +kernel)
def refined701Step17 : CertifiedDomain case701Family := refined701Step16.refineAgainst refined701Step9 (by decide +kernel) (by decide +kernel)
def refined701Step18 : CertifiedDomain case701Family := domain701_2_1.refineAgainst refined701Step11 (by decide +kernel) (by decide +kernel)
def refined701Step19 : CertifiedDomain case701Family := refined701Step4.refineAgainst refined701Step9 (by decide +kernel) (by decide +kernel)
def refined701Step20 : CertifiedDomain case701Family := refined701Step7.refineAgainst refined701Step11 (by decide +kernel) (by decide +kernel)
def refined701Step21 : CertifiedDomain case701Family := refined701Step20.refineAgainst refined701Step14 (by decide +kernel) (by decide +kernel)
def case701Domain0 : CertifiedDomain case701Family := domain701_0_0.enlarge [{2,12}] (by decide +kernel)
def case701Domain1 : CertifiedDomain case701Family := refined701Step1.enlarge [{0,10}] (by decide +kernel)
def case701Domain2 : CertifiedDomain case701Family := refined701Step18.enlarge [∅] (by decide +kernel)
def case701Domain3 : CertifiedDomain case701Family := domain701_3_0.enlarge [{7,17}] (by decide +kernel)
def case701Domain4 : CertifiedDomain case701Family := refined701Step2.enlarge [{9,19}] (by decide +kernel)
def case701Domain5 : CertifiedDomain case701Family := domain701_5_1.enlarge [∅,{3}] (by decide +kernel)
def case701Domain6 : CertifiedDomain case701Family := refined701Step19.enlarge [{4,13},{4,5,13}] (by decide +kernel)
def case701Domain7 : CertifiedDomain case701Family := refined701Step21.enlarge [{16},{5,16}] (by decide +kernel)
def case701Domain8 : CertifiedDomain case701Family := refined701Step9.enlarge [{1,11},{1,3,11}] (by decide +kernel)
def case701Domain9 : CertifiedDomain case701Family := refined701Step11.enlarge [{6,15}] (by decide +kernel)
def case701Domain10 : CertifiedDomain case701Family := refined701Step14.enlarge [{8,18}] (by decide +kernel)
def case701Domain11 : CertifiedDomain case701Family := refined701Step17.enlarge [{3,14},{5,14},{3,5,14}] (by decide +kernel)

end
end S12
