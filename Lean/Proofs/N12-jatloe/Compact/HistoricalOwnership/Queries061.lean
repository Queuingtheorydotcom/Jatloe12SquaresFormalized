import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1952 := ⟨512,1,{1,5,7},.hull ⟨(1,(12/5)),((113/50),1),((113/50),3),((33/20),(47/20)),(453/1673),(121/360)⟩⟩
checked_local_query query1953 := ⟨512,1,{2,5,7},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1954 := ⟨512,1,{3,5,7},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1955 := ⟨512,1,{4,5,7},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1956 := ⟨512,1,{0,6,7},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),3),((33/20),(33/20)),(121/256),(5/261)⟩⟩
checked_local_query query1957 := ⟨512,1,{1,6,7},.hull ⟨(1,(12/5)),((47/20),(33/20)),((113/50),3),((33/20),(47/20)),(151/445),(28/117)⟩⟩
checked_local_query query1958 := ⟨512,1,{2,6,7},.four ⟨true,false,true⟩ fourDatum91 fourDatum91_checked⟩
checked_local_query query1959 := ⟨512,1,{3,6,7},.four ⟨false,true,false⟩ fourDatum104 fourDatum104_checked⟩
checked_local_query query1960 := ⟨512,1,{4,6,7},.four ⟨false,true,false⟩ fourDatum103 fourDatum103_checked⟩
checked_local_query query1961 := ⟨512,1,{5,6,7},.four ⟨true,true,false⟩ fourDatum84 fourDatum84_checked⟩
checked_local_query query1962 := ⟨512,1,{0,1,8},.hull ⟨(1,(8/5)),(3,(8/5)),(1,(12/5)),((33/20),(33/20)),(26/75),(1/16)⟩⟩
checked_local_query query1963 := ⟨512,1,{0,2,8},.short ⟨⟨true,true,false⟩,.fiveLeft⟩ [⟨((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),0,0⟩,⟨((87/50),1),((87/50),1),((87/50),1),((87/50),1),0,0⟩]⟩
checked_local_query query1964 := ⟨512,1,{1,2,8},.hull ⟨(1,(12/5)),((87/50),1),(3,(8/5)),((33/20),(33/20)),(980/1853),(355/2208)⟩⟩
checked_local_query query1965 := ⟨512,1,{0,3,8},.hull ⟨(1,(8/5)),(3,(8/5)),((87/50),2),((33/20),(33/20)),(223/700),(1/8)⟩⟩
checked_local_query query1966 := ⟨512,1,{1,3,8},.short ⟨⟨true,true,false⟩,.fiveRight⟩ [⟨((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),0,0⟩,⟨(1,(12/5)),((47/20),(33/20)),(3,(8/5)),((87/50),2),(208/405),(1/28)⟩]⟩
checked_local_query query1967 := ⟨512,1,{2,3,8},.short ⟨⟨true,true,false⟩,.fiveLeft⟩ [⟨((87/50),1),(3,(8/5)),((87/50),2),((47/20),(33/20)),(610/807),(151/420)⟩,⟨((87/50),1),((87/50),1),((87/50),1),((87/50),1),0,0⟩]⟩
checked_local_query query1968 := ⟨512,1,{0,4,8},.hull ⟨(1,(8/5)),(3,(8/5)),((87/50),3),((33/20),(33/20)),(97/300),(1/28)⟩⟩
checked_local_query query1969 := ⟨512,1,{1,4,8},.hull ⟨(1,(12/5)),((47/20),(33/20)),((87/50),3),((33/20),(47/20)),(61/135),(4/13)⟩⟩
checked_local_query query1970 := ⟨512,1,{2,4,8},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1971 := ⟨512,1,{3,4,8},.hull ⟨((87/50),2),(3,(8/5)),((87/50),3),((113/50),2),(130/263),(52/315)⟩⟩
checked_local_query query1972 := ⟨512,1,{0,5,8},.four ⟨false,true,false⟩ fourDatum72 fourDatum72_checked⟩
checked_local_query query1973 := ⟨512,1,{1,5,8},.hull ⟨(1,(12/5)),((113/50),1),(3,(8/5)),((87/50),2),(52/315),(19/64)⟩⟩
checked_local_query query1974 := ⟨512,1,{4,5,8},.hull ⟨((87/50),3),((113/50),1),(3,(8/5)),((113/50),2),(133/318),(65/224)⟩⟩
checked_local_query query1975 := ⟨512,1,{0,6,8},.hull ⟨(1,(8/5)),(3,(8/5)),((113/50),2),((33/20),(33/20)),(197/700),(1/8)⟩⟩
checked_local_query query1976 := ⟨512,1,{1,6,8},.hull ⟨(1,(12/5)),((47/20),(33/20)),(3,(8/5)),((87/50),2),(208/405),(1/28)⟩⟩
checked_local_query query1977 := ⟨512,1,{4,6,8},.four ⟨false,true,false⟩ fourDatum69 fourDatum69_checked⟩
checked_local_query query1978 := ⟨512,1,{0,7,8},.hull ⟨(1,(8/5)),(3,(8/5)),((113/50),3),((33/20),(33/20)),(847/2700),(1/28)⟩⟩
checked_local_query query1979 := ⟨512,1,{1,7,8},.hull ⟨(1,(12/5)),((47/20),(33/20)),((113/50),3),((33/20),(47/20)),(151/445),(28/117)⟩⟩
checked_local_query query1980 := ⟨512,1,{2,7,8},.hull ⟨((87/50),1),(3,(8/5)),((113/50),3),((113/50),2),(26/63),(79/184)⟩⟩
checked_local_query query1981 := ⟨512,1,{3,7,8},.hull ⟨((87/50),2),((47/20),(33/20)),((113/50),3),((113/50),2),(52/61),(91/396)⟩⟩
checked_local_query query1982 := ⟨512,1,{4,7,8},.hull ⟨((87/50),3),((47/20),(33/20)),(3,(8/5)),((113/50),2),(532/755),(92/847)⟩⟩
checked_local_query query1983 := ⟨512,1,{5,7,8},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩

end N12Compact.HistoricalOwnership.Queries
