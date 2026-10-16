import Compact.Cases.C717.EntryDomains
import S12.DomainRefinement

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def refined717Step1 : CertifiedDomain case717Family := domain717_0_0.refineAgainst domain717_1_0 (by decide +kernel) (by decide +kernel)
def refined717Step2 : CertifiedDomain case717Family := domain717_3_0.refineAgainst domain717_4_0 (by decide +kernel) (by decide +kernel)
def refined717Step3 : CertifiedDomain case717Family := domain717_6_0.refineAgainst refined717Step1 (by decide +kernel) (by decide +kernel)
def refined717Step4 : CertifiedDomain case717Family := refined717Step3.refineAgainst domain717_1_0 (by decide +kernel) (by decide +kernel)
def refined717Step5 : CertifiedDomain case717Family := domain717_7_0.refineAgainst refined717Step2 (by decide +kernel) (by decide +kernel)
def refined717Step6 : CertifiedDomain case717Family := refined717Step5.refineAgainst domain717_4_0 (by decide +kernel) (by decide +kernel)
def refined717Step7 : CertifiedDomain case717Family := domain717_8_10.refineAgainst domain717_1_0 (by decide +kernel) (by decide +kernel)
def refined717Step8 : CertifiedDomain case717Family := domain717_9_13.refineAgainst refined717Step1 (by decide +kernel) (by decide +kernel)
def refined717Step9 : CertifiedDomain case717Family := domain717_10_10.refineAgainst domain717_4_0 (by decide +kernel) (by decide +kernel)
def refined717Step10 : CertifiedDomain case717Family := domain717_11_13.refineAgainst refined717Step2 (by decide +kernel) (by decide +kernel)
def refined717Step11 : CertifiedDomain case717Family := refined717Step10.refineAgainst refined717Step7 (by decide +kernel) (by decide +kernel)
def refined717Step12 : CertifiedDomain case717Family := domain717_2_2.refineAgainst refined717Step9 (by decide +kernel) (by decide +kernel)
def refined717Step13 : CertifiedDomain case717Family := domain717_5_2.refineAgainst refined717Step7 (by decide +kernel) (by decide +kernel)
def refined717Step14 : CertifiedDomain case717Family := refined717Step4.refineAgainst refined717Step8 (by decide +kernel) (by decide +kernel)
def refined717Step15 : CertifiedDomain case717Family := refined717Step14.refineAgainst refined717Step9 (by decide +kernel) (by decide +kernel)
def refined717Step16 : CertifiedDomain case717Family := refined717Step6.refineAgainst refined717Step7 (by decide +kernel) (by decide +kernel)
def refined717Step17 : CertifiedDomain case717Family := refined717Step16.refineAgainst refined717Step11 (by decide +kernel) (by decide +kernel)
def refined717Step18 : CertifiedDomain case717Family := refined717Step8.refineAgainst refined717Step9 (by decide +kernel) (by decide +kernel)
def case717Domain0 : CertifiedDomain case717Family := refined717Step1.enlarge [{2,12}] (by decide +kernel)
def case717Domain1 : CertifiedDomain case717Family := domain717_1_0.enlarge [{0,10}] (by decide +kernel)
def case717Domain2 : CertifiedDomain case717Family := refined717Step12.enlarge [∅] (by decide +kernel)
def case717Domain3 : CertifiedDomain case717Family := refined717Step2.enlarge [{7,17}] (by decide +kernel)
def case717Domain4 : CertifiedDomain case717Family := domain717_4_0.enlarge [{9,19}] (by decide +kernel)
def case717Domain5 : CertifiedDomain case717Family := refined717Step13.enlarge [∅] (by decide +kernel)
def case717Domain6 : CertifiedDomain case717Family := refined717Step15.enlarge [{4},{4,13},{4,16},{4,13,16}] (by decide +kernel)
def case717Domain7 : CertifiedDomain case717Family := refined717Step17.enlarge [{5},{5,13},{5,16},{5,13,16}] (by decide +kernel)
def case717Domain8 : CertifiedDomain case717Family := refined717Step7.enlarge [{1,11},{1,11,13}] (by decide +kernel)
def case717Domain9 : CertifiedDomain case717Family := refined717Step18.enlarge [{6,15}] (by decide +kernel)
def case717Domain10 : CertifiedDomain case717Family := refined717Step9.enlarge [{8,18},{8,16,18}] (by decide +kernel)
def case717Domain11 : CertifiedDomain case717Family := refined717Step11.enlarge [{3,14}] (by decide +kernel)

end
end S12
