import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query2048 := ⟨512,2,{8,12,13,16},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2049 := ⟨512,2,{8,12,15,16},.four ⟨true,false,false⟩ fourDatum73 fourDatum73_checked⟩
checked_local_query query2050 := ⟨512,2,{8,13,15,16},.hull ⟨((87/50),2),((113/50),1),(3,(87/50)),(2,(87/50)),(13/50),(78/703)⟩⟩
checked_local_query query2051 := ⟨512,2,{8,12,15,18},.four ⟨false,true,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query2052 := ⟨512,2,{8,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(8/5)),(2,(87/50)),(559/2318),(156/1315)⟩⟩
checked_local_query query2053 := ⟨512,2,{8,12,16,18},.four ⟨false,true,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query2054 := ⟨512,2,{8,13,16,18},.four ⟨false,true,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query2055 := ⟨512,2,{8,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(113/50)),(33/40),0⟩⟩
checked_local_query query2056 := ⟨512,2,{4,8,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(113/50)),(33/40),0⟩⟩
checked_local_query query2057 := ⟨512,2,{5,8,12,13,15},.hull ⟨((87/50),1),((113/50),1),(2,(113/50)),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2058 := ⟨512,2,{5,8,12,13,16},.hull ⟨((87/50),1),(3,(87/50)),(2,(113/50)),(2,(87/50)),(13/63),(925/1744)⟩⟩
checked_local_query query2059 := ⟨512,2,{5,8,12,15,16},.hull ⟨((87/50),1),((113/50),1),(2,(113/50)),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2060 := ⟨512,2,{5,8,13,15,16},.hull ⟨((87/50),2),((113/50),1),(3,(87/50)),(2,(87/50)),(13/50),(78/703)⟩⟩
checked_local_query query2061 := ⟨512,2,{5,8,12,15,18},.hull ⟨((87/50),1),((113/50),1),(2,(113/50)),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2062 := ⟨512,2,{5,8,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(8/5)),(2,(87/50)),(559/2318),(156/1315)⟩⟩
checked_local_query query2063 := ⟨512,2,{5,8,12,16,18},.hull ⟨((87/50),1),(3,(8/5)),(2,(113/50)),(2,(87/50)),(13/63),(647/1193)⟩⟩
checked_local_query query2064 := ⟨512,2,{5,8,13,16,18},.four ⟨false,true,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query2065 := ⟨512,2,{5,8,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(113/50)),(33/40),0⟩⟩
checked_local_query query2066 := ⟨512,2,{6,8,12,13,15},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2067 := ⟨512,2,{6,8,12,13,16},.hull ⟨((87/50),1),(3,(87/50)),((87/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query2068 := ⟨512,2,{6,8,12,15,16},.four ⟨true,true,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query2069 := ⟨512,2,{6,8,13,15,16},.hull ⟨((87/50),2),((113/50),1),(3,(87/50)),(2,(87/50)),(13/50),(78/703)⟩⟩
checked_local_query query2070 := ⟨512,2,{6,8,12,15,18},.four ⟨true,true,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query2071 := ⟨512,2,{6,8,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(8/5)),(2,(87/50)),(559/2318),(156/1315)⟩⟩
checked_local_query query2072 := ⟨512,2,{6,8,12,16,18},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query2073 := ⟨512,2,{6,8,13,16,18},.hull ⟨((87/50),2),((12/5),1),(3,(8/5)),(2,(87/50)),(559/2269),(221/2490)⟩⟩
checked_local_query query2074 := ⟨512,2,{6,8,16,18,19},.hull ⟨(3,(8/5)),(3,(12/5)),(3,(8/5)),(3,(113/50)),(33/40),0⟩⟩
checked_local_query query2075 := ⟨512,2,{4,9,12,13,15},.hull ⟨((87/50),1),(3,(113/50)),((87/50),2),((113/50),2),(50/63),(12/25)⟩⟩
checked_local_query query2076 := ⟨512,2,{4,9,12,15,18},.hull ⟨(3,(8/5)),(3,(113/50)),(3,(8/5)),(3,(87/50)),(7/33),0⟩⟩
checked_local_query query2077 := ⟨512,2,{4,9,13,15,18},.hull ⟨((87/50),2),((113/50),1),(3,(113/50)),((113/50),2),(169/1094),(325/872)⟩⟩
checked_local_query query2078 := ⟨512,2,{4,9,12,16,18},.hull ⟨(3,(8/5)),(3,(113/50)),(3,(8/5)),(3,(87/50)),(7/33),0⟩⟩
checked_local_query query2079 := ⟨512,2,{4,9,13,16,18},.hull ⟨(3,(8/5)),(3,(113/50)),(3,(8/5)),(3,(87/50)),(7/33),0⟩⟩

end N12Compact.HistoricalOwnership.Queries
