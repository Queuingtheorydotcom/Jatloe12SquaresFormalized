import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1760 := ⟨256,1,{2,3,7},.four ⟨true,true,true⟩ fourDatum85 fourDatum85_checked⟩
checked_local_query query1761 := ⟨256,1,{0,4,7},.hull ⟨(1,(8/5)),((33/20),(33/20)),((87/50),3),((33/20),(47/20)),(355/418),(455/873)⟩⟩
checked_local_query query1762 := ⟨256,1,{1,4,7},.hull ⟨(1,(12/5)),((33/20),(33/20)),((113/50),3),((33/20),(47/20)),(453/880),(91/267)⟩⟩
checked_local_query query1763 := ⟨256,1,{2,4,7},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1764 := ⟨256,1,{3,4,7},.four ⟨false,false,false⟩ fourDatum103 fourDatum103_checked⟩
checked_local_query query1765 := ⟨256,1,{0,5,7},.hull ⟨(1,(8/5)),((113/50),1),((113/50),3),((87/50),2),(133/393),(79/210)⟩⟩
checked_local_query query1766 := ⟨256,1,{1,5,7},.hull ⟨(1,(12/5)),((33/20),(33/20)),((113/50),3),((33/20),(47/20)),(453/880),(91/267)⟩⟩
checked_local_query query1767 := ⟨256,1,{2,5,7},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1768 := ⟨256,1,{3,5,7},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1769 := ⟨256,1,{4,5,7},.hull ⟨((33/20),(33/20)),((113/50),1),((87/50),3),((87/50),2),(9/61),(136/441)⟩⟩
checked_local_query query1770 := ⟨256,1,{0,6,7},.hull ⟨(1,(8/5)),((33/20),(33/20)),((113/50),3),((87/50),2),(133/156),(223/847)⟩⟩
checked_local_query query1771 := ⟨256,1,{1,6,7},.hull ⟨(1,(12/5)),((33/20),(33/20)),((113/50),3),((33/20),(47/20)),(453/880),(91/267)⟩⟩
checked_local_query query1772 := ⟨256,1,{2,6,7},.four ⟨true,false,false⟩ fourDatum85 fourDatum85_checked⟩
checked_local_query query1773 := ⟨256,1,{3,6,7},.four ⟨false,false,false⟩ fourDatum106 fourDatum106_checked⟩
checked_local_query query1774 := ⟨256,1,{4,6,7},.hull ⟨((33/20),(33/20)),((113/50),2),((87/50),3),((87/50),2),(9/61),(91/396)⟩⟩
checked_local_query query1775 := ⟨256,1,{5,6,7},.short ⟨⟨true,false,false⟩,.fiveLeft⟩ [⟨((33/20),(33/20)),((33/20),(33/20)),((33/20),(33/20)),((33/20),(33/20)),0,0⟩,⟨((113/50),1),((113/50),1),((113/50),1),((113/50),1),0,0⟩]⟩
checked_local_query query1776 := ⟨256,1,{0,1,8},.hull ⟨(1,(8/5)),(3,(8/5)),(1,(12/5)),((87/50),2),(37/50),(1/2)⟩⟩
checked_local_query query1777 := ⟨256,1,{0,2,8},.four ⟨false,false,false⟩ fourDatum72 fourDatum72_checked⟩
checked_local_query query1778 := ⟨256,1,{1,2,8},.hull ⟨(1,(12/5)),((87/50),1),(3,(8/5)),((87/50),2),(52/367),(185/552)⟩⟩
checked_local_query query1779 := ⟨256,1,{0,3,8},.hull ⟨(1,(8/5)),(3,(8/5)),((87/50),2),((47/20),(33/20)),(503/700),(1/8)⟩⟩
checked_local_query query1780 := ⟨256,1,{1,3,8},.hull ⟨(1,(12/5)),((33/20),(33/20)),(3,(8/5)),((47/20),(33/20)),(12/13),(15/28)⟩⟩
checked_local_query query1781 := ⟨256,1,{2,3,8},.hull ⟨((33/20),(33/20)),(3,(8/5)),((87/50),2),((47/20),(33/20)),(245/442),(35/477)⟩⟩
checked_local_query query1782 := ⟨256,1,{0,4,8},.hull ⟨(1,(8/5)),(3,(8/5)),((87/50),3),((33/20),(47/20)),(71/260),(15/28)⟩⟩
checked_local_query query1783 := ⟨256,1,{1,4,8},.hull ⟨(1,(12/5)),((33/20),(33/20)),((87/50),3),((33/20),(47/20)),(61/70),(13/27)⟩⟩
checked_local_query query1784 := ⟨256,1,{2,4,8},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1785 := ⟨256,1,{3,4,8},.hull ⟨((33/20),(33/20)),(3,(8/5)),((87/50),3),((113/50),2),(198/331),(503/1827)⟩⟩
checked_local_query query1786 := ⟨256,1,{0,5,8},.short ⟨⟨true,false,false⟩,.fiveLeft⟩ [⟨((33/20),(33/20)),((33/20),(33/20)),((33/20),(33/20)),((33/20),(33/20)),0,0⟩,⟨((113/50),1),((113/50),1),((113/50),1),((113/50),1),0,0⟩]⟩
checked_local_query query1787 := ⟨256,1,{1,5,8},.hull ⟨(1,(12/5)),((33/20),(33/20)),(3,(8/5)),((87/50),2),(208/685),(59/196)⟩⟩
checked_local_query query1788 := ⟨256,1,{2,5,8},.four ⟨true,false,false⟩ fourDatum74 fourDatum74_checked⟩
checked_local_query query1789 := ⟨256,1,{3,5,8},.hull ⟨((33/20),(33/20)),(3,(8/5)),((87/50),2),((47/20),(33/20)),(245/442),(35/477)⟩⟩
checked_local_query query1790 := ⟨256,1,{4,5,8},.hull ⟨((33/20),(33/20)),((113/50),1),((87/50),3),((87/50),2),(9/61),(136/441)⟩⟩
checked_local_query query1791 := ⟨256,1,{0,6,8},.hull ⟨(1,(8/5)),(3,(8/5)),((113/50),2),((47/20),(33/20)),(477/700),(1/8)⟩⟩

end N12Compact.HistoricalOwnership.Queries
