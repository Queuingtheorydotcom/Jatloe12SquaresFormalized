import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1024 := ⟨8192,1,{1,2,3},.hull ⟨(1,(12/5)),((87/50),1),((87/50),2),((33/20),(33/20)),(59/77),(71/148)⟩⟩
checked_local_query query1025 := ⟨8192,1,{0,1,4},.hull ⟨(1,(8/5)),(2,(457/500)),((87/50),3),((33/20),(33/20)),(4850/7843),(2755/10598)⟩⟩
checked_local_query query1026 := ⟨8192,1,{0,2,4},.hull ⟨(1,(8/5)),((87/50),1),((87/50),3),((33/20),(33/20)),(97/117),(427/1480)⟩⟩
checked_local_query query1027 := ⟨8192,1,{1,2,4},.hull ⟨(1,(12/5)),((87/50),1),((87/50),3),((33/20),(33/20)),(21/25),(71/296)⟩⟩
checked_local_query query1028 := ⟨8192,1,{0,3,4},.hull ⟨(1,(8/5)),(2,(457/500)),((87/50),3),((33/20),(33/20)),(4850/7843),(2755/10598)⟩⟩
checked_local_query query1029 := ⟨8192,1,{1,3,4},.hull ⟨(1,(12/5)),(2,(457/500)),((87/50),3),((33/20),(33/20)),(5250/8243),(10795/84982)⟩⟩
checked_local_query query1030 := ⟨8192,1,{2,3,4},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1031 := ⟨8192,1,{0,1,5},.hull ⟨(1,(8/5)),((113/50),1),(1,(12/5)),((33/20),(33/20)),(104/111),(151/336)⟩⟩
checked_local_query query1032 := ⟨8192,1,{1,2,5},.hull ⟨(1,(12/5)),((87/50),1),((113/50),1),((33/20),(33/20)),(35/373),(355/728)⟩⟩
checked_local_query query1033 := ⟨8192,1,{0,3,5},.hull ⟨(1,(8/5)),(2,(457/500)),((87/50),2),((33/20),(33/20)),(11150/20587),(24795/45382)⟩⟩
checked_local_query query1034 := ⟨8192,1,{1,3,5},.hull ⟨(1,(12/5)),(2,(457/500)),((113/50),1),((33/20),(33/20)),(1750/12823),(10795/23618)⟩⟩
checked_local_query query1035 := ⟨8192,1,{2,3,5},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1036 := ⟨8192,1,{0,4,5},.hull ⟨(1,(8/5)),(2,(457/500)),((87/50),3),((33/20),(33/20)),(4850/7843),(2755/10598)⟩⟩
checked_local_query query1037 := ⟨8192,1,{1,4,5},.hull ⟨(1,(12/5)),(2,(457/500)),((113/50),1),((33/20),(33/20)),(1750/12823),(10795/23618)⟩⟩
checked_local_query query1038 := ⟨8192,1,{2,4,5},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1039 := ⟨8192,1,{3,4,5},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1040 := ⟨8192,1,{0,1,6},.hull ⟨(1,(8/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(9850/38423),(24795/63218)⟩⟩
checked_local_query query1041 := ⟨8192,1,{0,2,6},.hull ⟨(1,(8/5)),((87/50),1),((113/50),2),((33/20),(33/20)),(197/625),(427/1052)⟩⟩
checked_local_query query1042 := ⟨8192,1,{1,2,6},.hull ⟨(1,(12/5)),((87/50),1),((113/50),2),((33/20),(33/20)),(685/1113),(355/1468)⟩⟩
checked_local_query query1043 := ⟨8192,1,{0,3,6},.hull ⟨(1,(8/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(9850/38423),(24795/63218)⟩⟩
checked_local_query query1044 := ⟨8192,1,{1,3,6},.hull ⟨(1,(12/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(34250/62823),(10795/73618)⟩⟩
checked_local_query query1045 := ⟨8192,1,{2,3,6},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1046 := ⟨8192,1,{0,4,6},.hull ⟨(1,(8/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(9850/38423),(24795/63218)⟩⟩
checked_local_query query1047 := ⟨8192,1,{1,4,6},.hull ⟨(1,(12/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(34250/62823),(10795/73618)⟩⟩
checked_local_query query1048 := ⟨8192,1,{2,4,6},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1049 := ⟨8192,1,{3,4,6},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1050 := ⟨8192,1,{0,5,6},.hull ⟨(1,(8/5)),(2,(457/500)),((113/50),2),((33/20),(33/20)),(9850/38423),(24795/63218)⟩⟩
checked_local_query query1051 := ⟨8192,1,{1,5,6},.hull ⟨(1,(12/5)),(2,(457/500)),((113/50),1),((33/20),(33/20)),(1750/12823),(10795/23618)⟩⟩
checked_local_query query1052 := ⟨8192,1,{2,5,6},.four ⟨true,true,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1053 := ⟨8192,1,{3,5,6},.four ⟨true,false,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1054 := ⟨8192,1,{4,5,6},.four ⟨true,true,false⟩ fourDatum21 fourDatum21_checked⟩
checked_local_query query1055 := ⟨8192,1,{0,1,7},.hull ⟨(1,(8/5)),(2,(457/500)),((113/50),3),((33/20),(33/20)),(42350/88423),(24795/113218)⟩⟩

end N12Compact.HistoricalOwnership.Queries
