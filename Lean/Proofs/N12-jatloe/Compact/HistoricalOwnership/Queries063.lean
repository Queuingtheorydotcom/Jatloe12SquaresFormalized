import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query2016 := ⟨512,1,{3,8,9},.hull ⟨((87/50),2),((47/20),(33/20)),(3,(12/5)),((113/50),2),(208/503),(182/685)⟩⟩
checked_local_query query2017 := ⟨512,1,{4,8,9},.hull ⟨((87/50),3),((47/20),(33/20)),(3,(8/5)),((113/50),2),(532/755),(92/847)⟩⟩
checked_local_query query2018 := ⟨512,1,{5,8,9},.four ⟨false,true,false⟩ fourDatum65 fourDatum65_checked⟩
checked_local_query query2019 := ⟨512,1,{7,8,9},.hull ⟨((113/50),3),((47/20),(33/20)),(3,(8/5)),((47/20),(47/20)),(71/162),(7/97)⟩⟩
checked_local_query query2020 := ⟨512,2,{4,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2021 := ⟨512,2,{2,4,12,13,15},.four ⟨true,true,false⟩ fourDatum110 fourDatum110_checked⟩
checked_local_query query2022 := ⟨512,2,{2,4,12,13,16},.four ⟨true,true,false⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query2023 := ⟨512,2,{2,4,12,15,16},.four ⟨true,true,false⟩ fourDatum109 fourDatum109_checked⟩
checked_local_query query2024 := ⟨512,2,{2,4,13,15,16},.hull ⟨((8/5),1),((113/50),1),((8/5),1),((87/50),1),(7/33),0⟩⟩
checked_local_query query2025 := ⟨512,2,{2,4,12,15,18},.four ⟨false,true,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query2026 := ⟨512,2,{2,4,13,15,18},.hull ⟨((8/5),1),((113/50),1),((8/5),1),((87/50),1),(7/33),0⟩⟩
checked_local_query query2027 := ⟨512,2,{2,4,12,16,18},.four ⟨false,true,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query2028 := ⟨512,2,{2,4,13,16,18},.four ⟨false,true,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query2029 := ⟨512,2,{2,4,15,16,18},.hull ⟨((8/5),1),((113/50),1),((8/5),1),((87/50),1),(7/33),0⟩⟩
checked_local_query query2030 := ⟨512,2,{2,4,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2031 := ⟨512,2,{4,5,12,13,15},.four ⟨true,true,false⟩ fourDatum77 fourDatum77_checked⟩
checked_local_query query2032 := ⟨512,2,{4,5,12,15,18},.hull ⟨((87/50),1),(3,(8/5)),(2,(113/50)),((113/50),2),(76/93),(790/1193)⟩⟩
checked_local_query query2033 := ⟨512,2,{4,5,13,15,18},.hull ⟨((87/50),2),(3,(8/5)),(2,(113/50)),((113/50),2),(26/43),(40/83)⟩⟩
checked_local_query query2034 := ⟨512,2,{4,5,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2035 := ⟨512,2,{6,12,13,15},.hull ⟨((87/50),1),((47/20),(33/20)),((87/50),2),(2,(87/50)),(50/63),(706/1525)⟩⟩
checked_local_query query2036 := ⟨512,2,{6,12,13,16},.hull ⟨((87/50),1),((47/20),(33/20)),((87/50),2),(2,(87/50)),(50/63),(706/1525)⟩⟩
checked_local_query query2037 := ⟨512,2,{6,12,15,16},.four ⟨true,true,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query2038 := ⟨512,2,{6,13,15,16},.hull ⟨((87/50),2),((113/50),1),((47/20),(33/20)),(2,(87/50)),(169/758),(156/535)⟩⟩
checked_local_query query2039 := ⟨512,2,{6,12,15,18},.four ⟨true,true,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query2040 := ⟨512,2,{6,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(8/5)),(2,(87/50)),(559/2318),(156/1315)⟩⟩
checked_local_query query2041 := ⟨512,2,{6,12,16,18},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query2042 := ⟨512,2,{6,13,16,18},.hull ⟨((87/50),2),((12/5),1),(3,(8/5)),(2,(87/50)),(559/2269),(221/2490)⟩⟩
checked_local_query query2043 := ⟨512,2,{6,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2044 := ⟨512,2,{4,6,12,13,16},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query2045 := ⟨512,2,{4,6,12,16,18},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query2046 := ⟨512,2,{4,6,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(87/50)),(7/40),0⟩⟩
checked_local_query query2047 := ⟨512,2,{8,12,13,15},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩

end N12Compact.HistoricalOwnership.Queries
