import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query800 := ⟨192,1,{5,7},.hull ⟨((457/500),3),((113/50),1),((113/50),3),((33/20),(47/20)),(8749/20949),(5971/26920)⟩⟩
checked_local_query query801 := ⟨192,1,{6,7},.hull ⟨((457/500),3),((113/50),3),((457/500),3),((87/50),3),(413/673),0⟩⟩
checked_local_query query802 := ⟨192,1,{8},.four ⟨true,false,true⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query803 := ⟨192,1,{0,8},.hull ⟨(1,(8/5)),(1,(1543/500)),(1,(8/5)),(1,(12/5)),(400/743),0⟩⟩
checked_local_query query804 := ⟨192,1,{1,8},.hull ⟨((457/500),3),(1,(12/5)),(3,(8/5)),((33/20),(47/20)),(31/71),(551/1616)⟩⟩
checked_local_query query805 := ⟨192,1,{2,8},.hull ⟨((457/500),3),((87/50),1),(3,(8/5)),((33/20),(33/20)),(17857/26587),(3569/30156)⟩⟩
checked_local_query query806 := ⟨192,1,{3,8},.hull ⟨((457/500),3),((87/50),2),(3,(8/5)),((33/20),(47/20)),(217/487),(1991/9296)⟩⟩
checked_local_query query807 := ⟨192,1,{4,8},.four ⟨true,false,true⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query808 := ⟨192,1,{5,8},.hull ⟨((457/500),3),((113/50),1),(3,(8/5)),((33/20),(47/20)),(31/161),(853/3268)⟩⟩
checked_local_query query809 := ⟨192,1,{6,8},.four ⟨true,false,true⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query810 := ⟨192,1,{7,8},.hull ⟨((457/500),3),((113/50),3),((457/500),3),((87/50),3),(413/673),0⟩⟩
checked_local_query query811 := ⟨192,1,{9},.four ⟨true,false,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query812 := ⟨192,1,{0,9},.hull ⟨(1,(8/5)),(1,(1543/500)),(1,(8/5)),(1,(12/5)),(400/743),0⟩⟩
checked_local_query query813 := ⟨192,1,{1,9},.four ⟨true,false,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query814 := ⟨192,1,{2,9},.hull ⟨((457/500),3),((87/50),1),(3,(12/5)),((33/20),(33/20)),(1583/2213),(3569/36764)⟩⟩
checked_local_query query815 := ⟨192,1,{3,9},.hull ⟨((457/500),3),((87/50),2),(3,(12/5)),((33/20),(47/20)),(9143/13913),(1991/15904)⟩⟩
checked_local_query query816 := ⟨192,1,{4,9},.four ⟨true,false,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query817 := ⟨192,1,{5,9},.hull ⟨((457/500),3),((113/50),1),(3,(12/5)),((33/20),(47/20)),(9143/27673),(5971/33644)⟩⟩
checked_local_query query818 := ⟨192,1,{6,9},.hull ⟨((457/500),3),((113/50),2),(3,(12/5)),((47/20),(47/20)),(4943/7173),(5611/12784)⟩⟩
checked_local_query query819 := ⟨192,1,{7,9},.hull ⟨((457/500),3),((113/50),3),((457/500),3),((87/50),3),(413/673),0⟩⟩
checked_local_query query820 := ⟨192,1,{8,9},.hull ⟨((457/500),3),(3,(8/5)),(3,(12/5)),((47/20),(47/20)),(4943/10143),(935/2384)⟩⟩
checked_local_query query821 := ⟨192,2,{14},.hull ⟨((457/500),3),((87/50),3),((457/500),3),((8/5),3),(49/59),0⟩⟩
checked_local_query query822 := ⟨192,2,{11,14},.hull ⟨((457/500),3),((87/50),3),((457/500),3),((8/5),3),(49/59),0⟩⟩
checked_local_query query823 := ⟨768,1,{1},.four ⟨false,false,false⟩ fourDatum92 fourDatum92_checked⟩
checked_local_query query824 := ⟨768,1,{0,1},.four ⟨false,false,false⟩ fourDatum65 fourDatum65_checked⟩
checked_local_query query825 := ⟨768,1,{1,2},.four ⟨true,false,false⟩ fourDatum80 fourDatum80_checked⟩
checked_local_query query826 := ⟨768,1,{1,3},.four ⟨false,false,false⟩ fourDatum97 fourDatum97_checked⟩
checked_local_query query827 := ⟨768,1,{4},.hull ⟨((33/20),(33/20)),((47/20),(33/20)),((87/50),3),((87/50),2),(9/70),(7/27)⟩⟩
checked_local_query query828 := ⟨768,1,{0,4},.hull ⟨(1,(8/5)),((47/20),(33/20)),((87/50),3),((33/20),(47/20)),(355/873),(980/1853)⟩⟩
checked_local_query query829 := ⟨768,1,{1,4},.hull ⟨(1,(12/5)),((33/20),(33/20)),((87/50),3),((33/20),(47/20)),(61/70),(13/27)⟩⟩
checked_local_query query830 := ⟨768,1,{2,4},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query831 := ⟨768,1,{3,4},.four ⟨false,false,false⟩ fourDatum103 fourDatum103_checked⟩

end N12Compact.HistoricalOwnership.Queries
