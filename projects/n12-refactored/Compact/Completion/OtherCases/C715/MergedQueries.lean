import Compact.Completion.OtherCases.C715.RowIdentity
import Compact.Bridge.SharedLocalQueries
import Compact.Bridge.SmallOwnerDomain

/-! Exact local refutations for the genuine merged owner of markers 10 and 14.
Each rational certificate is checked by ordinary kernel reduction. F labels
retain every subset of size one or two; G labels have size one. -/

namespace N12Compact.Completion.OtherCases.C715
open S12 S12Pilot
set_option Elab.async false
noncomputable section

checked_local_query mergedFQuery1 := ⟨17408,0,{0},.four ⟨false,true,true⟩ fourDatum36 fourDatum36_checked⟩
checked_local_query mergedFQuery2 := ⟨17408,0,{1},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(113/50)),(2,(113/50)),(9/35),(9437/26937)⟩⟩
checked_local_query mergedFQuery4 := ⟨17408,0,{2},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery8 := ⟨17408,0,{3},.four ⟨false,true,true⟩ fourDatum28 fourDatum28_checked⟩
checked_local_query mergedFQuery16 := ⟨17408,0,{4},.short ⟨⟨false,true,true⟩,.fiveRight⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(2,(87/50)),(2,(87/50)),(2,(87/50)),(2,(87/50)),0,0⟩]⟩
checked_local_query mergedFQuery64 := ⟨17408,0,{6},.four ⟨false,true,false⟩ fourDatum14 fourDatum14_checked⟩
checked_local_query mergedFQuery256 := ⟨17408,0,{8},.short ⟨⟨false,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(3,(87/50)),(3,(87/50)),(3,(87/50)),(3,(87/50)),0,0⟩]⟩
checked_local_query mergedFQuery3 := ⟨17408,0,{0,1},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(113/50)),(2,(113/50)),(9/35),(9437/26937)⟩⟩
checked_local_query mergedFQuery5 := ⟨17408,0,{0,2},.hull ⟨((47/20),(47/20)),(1,(87/50)),((8/5),1),((33/20),(33/20)),(60/121),(74/195)⟩⟩
checked_local_query mergedFQuery9 := ⟨17408,0,{0,3},.hull ⟨((47/20),(47/20)),(1,(87/50)),((8/5),3),((33/20),(47/20)),(455/908),(427/1335)⟩⟩
checked_local_query mergedFQuery17 := ⟨17408,0,{0,4},.four ⟨false,true,true⟩ fourDatum36 fourDatum36_checked⟩
checked_local_query mergedFQuery33 := ⟨17408,0,{0,5},.four ⟨false,true,true⟩ fourDatum37 fourDatum37_checked⟩
checked_local_query mergedFQuery65 := ⟨17408,0,{0,6},.hull ⟨((47/20),(47/20)),(1,(87/50)),((12/5),1),((33/20),(33/20)),(196/267),(518/1853)⟩⟩
checked_local_query mergedFQuery129 := ⟨17408,0,{0,7},.hull ⟨((47/20),(47/20)),(1,(87/50)),((12/5),3),(2,(113/50)),(223/755),(92/847)⟩⟩
checked_local_query mergedFQuery257 := ⟨17408,0,{0,8},.hull ⟨(1,(87/50)),(3,(87/50)),(1,(87/50)),(2,(87/50)),(1/2),0⟩⟩
checked_local_query mergedFQuery513 := ⟨17408,0,{0,9},.four ⟨false,true,true⟩ fourDatum36 fourDatum36_checked⟩
checked_local_query mergedFQuery6 := ⟨17408,0,{1,2},.hull ⟨((47/20),(47/20)),(1,(113/50)),((8/5),1),((33/20),(33/20)),(140/291),(98/195)⟩⟩
checked_local_query mergedFQuery10 := ⟨17408,0,{1,3},.hull ⟨((47/20),(47/20)),(1,(113/50)),((8/5),3),((33/20),(47/20)),(65/126),(1/15)⟩⟩
checked_local_query mergedFQuery18 := ⟨17408,0,{1,4},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(113/50)),(2,(113/50)),(9/35),(9437/26937)⟩⟩
checked_local_query mergedFQuery34 := ⟨17408,0,{1,5},.four ⟨false,true,true⟩ fourDatum34 fourDatum34_checked⟩
checked_local_query mergedFQuery66 := ⟨17408,0,{1,6},.hull ⟨((47/20),(47/20)),(1,(113/50)),((12/5),1),((47/20),(33/20)),(5/126),(15/29)⟩⟩
checked_local_query mergedFQuery130 := ⟨17408,0,{1,7},.hull ⟨((47/20),(47/20)),(1,(113/50)),((12/5),3),((33/20),(47/20)),(91/162),(7/97)⟩⟩
checked_local_query mergedFQuery258 := ⟨17408,0,{1,8},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(113/50)),(2,(113/50)),(9/35),(9437/26937)⟩⟩
checked_local_query mergedFQuery514 := ⟨17408,0,{1,9},.hull ⟨(1,(113/50)),(3,(113/50)),(1,(113/50)),(2,(113/50)),(1/2),0⟩⟩
checked_local_query mergedFQuery12 := ⟨17408,0,{2,3},.hull ⟨((47/20),(47/20)),((8/5),1),((8/5),3),((33/20),(33/20)),(49/54),(7/25)⟩⟩
checked_local_query mergedFQuery20 := ⟨17408,0,{2,4},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery36 := ⟨17408,0,{2,5},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery68 := ⟨17408,0,{2,6},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery132 := ⟨17408,0,{2,7},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery260 := ⟨17408,0,{2,8},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery516 := ⟨17408,0,{2,9},.hull ⟨((47/20),(47/20)),((1543/500),2),((8/5),1),((47/20),(33/20)),(5250/7409),(5152/12561)⟩⟩
checked_local_query mergedFQuery24 := ⟨17408,0,{3,4},.hull ⟨((47/20),(47/20)),((8/5),3),(2,(87/50)),(2,(113/50)),(7/15),(59/137)⟩⟩
checked_local_query mergedFQuery40 := ⟨17408,0,{3,5},.four ⟨false,true,true⟩ fourDatum29 fourDatum29_checked⟩
checked_local_query mergedFQuery72 := ⟨17408,0,{3,6},.hull ⟨((47/20),(47/20)),((8/5),3),((12/5),1),((47/20),(33/20)),(1/13),(15/28)⟩⟩
checked_local_query mergedFQuery136 := ⟨17408,0,{3,7},.four ⟨false,true,true⟩ fourDatum30 fourDatum30_checked⟩
checked_local_query mergedFQuery264 := ⟨17408,0,{3,8},.four ⟨false,true,true⟩ fourDatum28 fourDatum28_checked⟩
checked_local_query mergedFQuery520 := ⟨17408,0,{3,9},.four ⟨false,true,true⟩ fourDatum28 fourDatum28_checked⟩
checked_local_query mergedFQuery80 := ⟨17408,0,{4,6},.hull ⟨((47/20),(47/20)),(2,(87/50)),((12/5),1),((47/20),(33/20)),(35/258),(245/503)⟩⟩
checked_local_query mergedFQuery144 := ⟨17408,0,{4,7},.short ⟨⟨false,true,true⟩,.fiveRight⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(2,(87/50)),(2,(87/50)),(2,(87/50)),(2,(87/50)),0,0⟩]⟩
checked_local_query mergedFQuery272 := ⟨17408,0,{4,8},.short ⟨⟨false,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(3,(87/50)),(3,(87/50)),(3,(87/50)),(3,(87/50)),0,0⟩]⟩
checked_local_query mergedFQuery96 := ⟨17408,0,{5,6},.hull ⟨((47/20),(47/20)),(2,(113/50)),((12/5),1),((47/20),(33/20)),(35/232),(245/477)⟩⟩
checked_local_query mergedFQuery192 := ⟨17408,0,{6,7},.four ⟨false,true,false⟩ fourDatum14 fourDatum14_checked⟩
checked_local_query mergedFQuery320 := ⟨17408,0,{6,8},.short ⟨⟨false,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(3,(87/50)),(3,(87/50)),(3,(87/50)),(3,(87/50)),0,0⟩]⟩
checked_local_query mergedFQuery576 := ⟨17408,0,{6,9},.four ⟨false,true,false⟩ fourDatum14 fourDatum14_checked⟩
checked_local_query mergedFQuery384 := ⟨17408,0,{7,8},.short ⟨⟨false,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨(3,(87/50)),(3,(87/50)),(3,(87/50)),(3,(87/50)),0,0⟩]⟩

def mergedF : DirectSingleDomain :=
  ⟨17408,1,2,[{5},{7},{9},{4,5},{4,9},{5,7},{5,8},{5,9},{7,9},{8,9}],[
    mergedFQuery1_certified,
    mergedFQuery2_certified,
    mergedFQuery4_certified,
    mergedFQuery8_certified,
    mergedFQuery16_certified,
    mergedFQuery64_certified,
    mergedFQuery256_certified,
    mergedFQuery3_certified,
    mergedFQuery5_certified,
    mergedFQuery9_certified,
    mergedFQuery17_certified,
    mergedFQuery33_certified,
    mergedFQuery65_certified,
    mergedFQuery129_certified,
    mergedFQuery257_certified,
    mergedFQuery513_certified,
    mergedFQuery6_certified,
    mergedFQuery10_certified,
    mergedFQuery18_certified,
    mergedFQuery34_certified,
    mergedFQuery66_certified,
    mergedFQuery130_certified,
    mergedFQuery258_certified,
    mergedFQuery514_certified,
    mergedFQuery12_certified,
    mergedFQuery20_certified,
    mergedFQuery36_certified,
    mergedFQuery68_certified,
    mergedFQuery132_certified,
    mergedFQuery260_certified,
    mergedFQuery516_certified,
    mergedFQuery24_certified,
    mergedFQuery40_certified,
    mergedFQuery72_certified,
    mergedFQuery136_certified,
    mergedFQuery264_certified,
    mergedFQuery520_certified,
    mergedFQuery80_certified,
    mergedFQuery144_certified,
    mergedFQuery272_certified,
    mergedFQuery96_certified,
    mergedFQuery192_certified,
    mergedFQuery320_certified,
    mergedFQuery576_certified,
    mergedFQuery384_certified]⟩

private def mergedFSignatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(17408,0,{0}),(17408,0,{1}),(17408,0,{2}),(17408,0,{3}),(17408,0,{4}),(17408,0,{6}),(17408,0,{8}),(17408,0,{0,1}),(17408,0,{0,2}),(17408,0,{0,3}),(17408,0,{0,4}),(17408,0,{0,5}),(17408,0,{0,6}),(17408,0,{0,7}),(17408,0,{0,8}),(17408,0,{0,9}),(17408,0,{1,2}),(17408,0,{1,3}),(17408,0,{1,4}),(17408,0,{1,5}),(17408,0,{1,6}),(17408,0,{1,7}),(17408,0,{1,8}),(17408,0,{1,9}),(17408,0,{2,3}),(17408,0,{2,4}),(17408,0,{2,5}),(17408,0,{2,6}),(17408,0,{2,7}),(17408,0,{2,8}),(17408,0,{2,9}),(17408,0,{3,4}),(17408,0,{3,5}),(17408,0,{3,6}),(17408,0,{3,7}),(17408,0,{3,8}),(17408,0,{3,9}),(17408,0,{4,6}),(17408,0,{4,7}),(17408,0,{4,8}),(17408,0,{5,6}),(17408,0,{6,7}),(17408,0,{6,8}),(17408,0,{6,9}),(17408,0,{7,8})]

theorem mergedF_checked : mergedF.Check family 0 :=
  N12Compact.SmallOwnerDomain.checked mergedF family 0
    mergedFSignatures (by rfl) (by decide +kernel) (by decide +kernel)

checked_local_query mergedGQuery1 := ⟨17408,1,{0},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(8/5)),((87/50),2),(75/2767),(4711/10245)⟩⟩
checked_local_query mergedGQuery2 := ⟨17408,1,{1},.hull ⟨((47/20),(47/20)),((1543/500),2),(1,(12/5)),((33/20),(47/20)),(350/1907),(2450/4357)⟩⟩
checked_local_query mergedGQuery4 := ⟨17408,1,{2},.hull ⟨((47/20),(47/20)),((1543/500),2),((87/50),1),((47/20),(33/20)),(4270/6919),(5152/12071)⟩⟩
checked_local_query mergedGQuery8 := ⟨17408,1,{3},.hull ⟨((1543/500),2),((87/50),2),((1543/500),2),((113/50),2),(413/673),0⟩⟩
checked_local_query mergedGQuery16 := ⟨17408,1,{4},.short ⟨⟨true,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨((87/50),3),((87/50),3),((87/50),3),((87/50),3),0,0⟩]⟩
checked_local_query mergedGQuery32 := ⟨17408,1,{5},.hull ⟨((47/20),(47/20)),((1543/500),2),((113/50),1),((47/20),(33/20)),(630/5099),(5152/10251)⟩⟩
checked_local_query mergedGQuery128 := ⟨17408,1,{7},.four ⟨false,true,true⟩ fourDatum18 fourDatum18_checked⟩

def mergedG : DirectSingleDomain :=
  ⟨17408,1,1,[{6},{8},{9}],[
    mergedGQuery1_certified,
    mergedGQuery2_certified,
    mergedGQuery4_certified,
    mergedGQuery8_certified,
    mergedGQuery16_certified,
    mergedGQuery32_certified,
    mergedGQuery128_certified]⟩

private def mergedGSignatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(17408,1,{0}),(17408,1,{1}),(17408,1,{2}),(17408,1,{3}),(17408,1,{4}),(17408,1,{5}),(17408,1,{7})]

theorem mergedG_checked : mergedG.Check family 1 :=
  N12Compact.SmallOwnerDomain.checked mergedG family 1
    mergedGSignatures (by rfl) (by decide +kernel) (by decide +kernel)

end
end N12Compact.Completion.OtherCases.C715
