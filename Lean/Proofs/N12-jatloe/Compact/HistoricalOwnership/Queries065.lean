import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query2080 := ⟨512,2,{4,9,15,16,18},.hull ⟨(3,(8/5)),(3,(113/50)),(3,(8/5)),(3,(87/50)),(7/33),0⟩⟩
checked_local_query query2081 := ⟨512,2,{4,9,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2082 := ⟨512,2,{8,9,12,13,15},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2083 := ⟨512,2,{8,9,12,13,16},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2084 := ⟨512,2,{8,9,12,15,16},.four ⟨true,false,false⟩ fourDatum73 fourDatum73_checked⟩
checked_local_query query2085 := ⟨512,2,{8,9,13,15,16},.hull ⟨((87/50),2),((113/50),1),(3,(87/50)),(2,(87/50)),(13/50),(78/703)⟩⟩
checked_local_query query2086 := ⟨512,2,{8,9,12,15,18},.four ⟨false,true,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query2087 := ⟨512,2,{8,9,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(8/5)),(2,(87/50)),(559/2318),(156/1315)⟩⟩
checked_local_query query2088 := ⟨512,2,{8,9,12,16,18},.four ⟨false,true,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query2089 := ⟨512,2,{8,9,13,16,18},.four ⟨false,true,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query2090 := ⟨3072,0,{0,1},.hull ⟨(1,(87/50)),((47/20),(47/20)),((33/20),(47/20)),(2,(113/50)),(272/335),(92/427)⟩⟩
checked_local_query query2091 := ⟨3072,0,{0,2},.hull ⟨(1,(87/50)),((8/5),1),((47/20),(47/20)),((33/20),(33/20)),(37/67),(61/195)⟩⟩
checked_local_query query2092 := ⟨3072,0,{1,2},.hull ⟨(1,(113/50)),((8/5),1),((47/20),(47/20)),((33/20),(33/20)),(21/31),(151/585)⟩⟩
checked_local_query query2093 := ⟨3072,0,{0,3},.hull ⟨(1,(87/50)),((47/20),(47/20)),((8/5),3),(2,(113/50)),(948/1243),(92/1335)⟩⟩
checked_local_query query2094 := ⟨3072,0,{1,3},.four ⟨false,false,true⟩ fourDatum79 fourDatum79_checked⟩
checked_local_query query2095 := ⟨3072,0,{2,3},.hull ⟨((8/5),1),((47/20),(47/20)),((8/5),3),((33/20),(33/20)),(5/54),(7/25)⟩⟩
checked_local_query query2096 := ⟨3072,0,{0,4},.hull ⟨(1,(87/50)),((47/20),(47/20)),((33/20),(47/20)),(2,(113/50)),(272/335),(92/427)⟩⟩
checked_local_query query2097 := ⟨3072,0,{1,4},.hull ⟨(1,(113/50)),(2,(87/50)),((47/20),(47/20)),(2,(113/50)),(45/136),(65/99)⟩⟩
checked_local_query query2098 := ⟨3072,0,{2,4},.hull ⟨((8/5),1),((47/20),(47/20)),((33/20),(47/20)),((33/20),(33/20)),(1/15),(4/9)⟩⟩
checked_local_query query2099 := ⟨3072,0,{3,4},.hull ⟨((8/5),3),(2,(87/50)),((47/20),(47/20)),(2,(113/50)),(295/477),(208/685)⟩⟩
checked_local_query query2100 := ⟨3072,0,{2,5},.hull ⟨((8/5),1),((47/20),(47/20)),((33/20),(47/20)),((33/20),(33/20)),(1/15),(4/9)⟩⟩
checked_local_query query2101 := ⟨3072,0,{0,6},.hull ⟨(1,(87/50)),((12/5),1),((47/20),(47/20)),((33/20),(33/20)),(37/107),(355/1853)⟩⟩
checked_local_query query2102 := ⟨3072,0,{1,6},.hull ⟨(1,(113/50)),((12/5),1),((47/20),(47/20)),(2,(87/50)),(792/1295),(76/261)⟩⟩
checked_local_query query2103 := ⟨3072,0,{2,6},.hull ⟨((8/5),1),((12/5),1),((33/20),(47/20)),((33/20),(33/20)),(1/16),(13/27)⟩⟩
checked_local_query query2104 := ⟨3072,0,{3,6},.hull ⟨((8/5),3),((33/20),(47/20)),((12/5),1),(2,(87/50)),(208/223),(197/420)⟩⟩
checked_local_query query2105 := ⟨3072,0,{4,6},.hull ⟨((33/20),(47/20)),((12/5),1),((47/20),(47/20)),(2,(113/50)),(7/60),(3/7)⟩⟩
checked_local_query query2106 := ⟨3072,0,{5,6},.hull ⟨((33/20),(47/20)),((12/5),1),((47/20),(47/20)),(2,(87/50)),(427/930),(1/63)⟩⟩
checked_local_query query2107 := ⟨3072,0,{0,7},.hull ⟨(1,(87/50)),((47/20),(47/20)),((12/5),3),(2,(113/50)),(532/755),(92/847)⟩⟩
checked_local_query query2108 := ⟨3072,0,{1,7},.four ⟨false,false,true⟩ fourDatum78 fourDatum78_checked⟩
checked_local_query query2109 := ⟨3072,0,{2,7},.hull ⟨((8/5),1),((47/20),(47/20)),((33/20),(47/20)),((33/20),(33/20)),(1/15),(4/9)⟩⟩
checked_local_query query2110 := ⟨3072,0,{3,7},.four ⟨true,false,true⟩ fourDatum65 fourDatum65_checked⟩
checked_local_query query2111 := ⟨3072,0,{4,7},.hull ⟨((33/20),(47/20)),(2,(87/50)),((47/20),(47/20)),(2,(113/50)),(9/35),(26/61)⟩⟩

end N12Compact.HistoricalOwnership.Queries
