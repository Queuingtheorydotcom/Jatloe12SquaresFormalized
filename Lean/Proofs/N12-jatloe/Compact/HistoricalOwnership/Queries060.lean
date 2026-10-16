import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1920 := ⟨512,1,{0,1,5},.hull ⟨(1,(8/5)),((113/50),1),(1,(12/5)),((33/20),(33/20)),(104/111),(151/336)⟩⟩
checked_local_query query1921 := ⟨512,1,{0,2,5},.four ⟨true,true,false⟩ fourDatum74 fourDatum74_checked⟩
checked_local_query query1922 := ⟨512,1,{1,2,5},.hull ⟨(1,(12/5)),((87/50),1),((113/50),1),((33/20),(33/20)),(35/373),(355/728)⟩⟩
checked_local_query query1923 := ⟨512,1,{0,3,5},.hull ⟨(1,(8/5)),((113/50),1),((87/50),2),((33/20),(33/20)),(223/495),(151/316)⟩⟩
checked_local_query query1924 := ⟨512,1,{1,3,5},.four ⟨false,false,true⟩ fourDatum69 fourDatum69_checked⟩
checked_local_query query1925 := ⟨512,1,{0,4,5},.hull ⟨(1,(8/5)),((113/50),1),((87/50),3),((33/20),(33/20)),(97/195),(151/736)⟩⟩
checked_local_query query1926 := ⟨512,1,{1,4,5},.hull ⟨(1,(12/5)),((113/50),1),((87/50),3),((33/20),(47/20)),(61/135),(121/256)⟩⟩
checked_local_query query1927 := ⟨512,1,{2,4,5},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1928 := ⟨512,1,{3,4,5},.four ⟨true,true,false⟩ fourDatum85 fourDatum85_checked⟩
checked_local_query query1929 := ⟨512,1,{0,1,6},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),2),((33/20),(33/20)),(197/442),(35/477)⟩⟩
checked_local_query query1930 := ⟨512,1,{0,2,6},.hull ⟨(1,(8/5)),((87/50),1),((113/50),2),((33/20),(33/20)),(197/625),(427/1052)⟩⟩
checked_local_query query1931 := ⟨512,1,{1,2,6},.hull ⟨(1,(12/5)),((87/50),1),((47/20),(33/20)),((33/20),(33/20)),(15/28),(71/267)⟩⟩
checked_local_query query1932 := ⟨512,1,{0,3,6},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),2),((33/20),(33/20)),(197/442),(35/477)⟩⟩
checked_local_query query1933 := ⟨512,1,{1,3,6},.four ⟨false,false,false⟩ fourDatum96 fourDatum96_checked⟩
checked_local_query query1934 := ⟨512,1,{0,4,6},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),2),((33/20),(33/20)),(197/442),(35/477)⟩⟩
checked_local_query query1935 := ⟨512,1,{1,4,6},.hull ⟨(1,(12/5)),((47/20),(33/20)),((87/50),3),((33/20),(47/20)),(61/135),(4/13)⟩⟩
checked_local_query query1936 := ⟨512,1,{2,4,6},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1937 := ⟨512,1,{3,4,6},.four ⟨false,true,false⟩ fourDatum106 fourDatum106_checked⟩
checked_local_query query1938 := ⟨512,1,{0,5,6},.hull ⟨(1,(8/5)),((113/50),1),((113/50),2),((33/20),(33/20)),(197/807),(151/420)⟩⟩
checked_local_query query1939 := ⟨512,1,{1,5,6},.hull ⟨(1,(12/5)),((113/50),1),((113/50),2),((87/50),2),(2/7),(19/45)⟩⟩
checked_local_query query1940 := ⟨512,1,{4,5,6},.four ⟨true,false,true⟩ fourDatum85 fourDatum85_checked⟩
checked_local_query query1941 := ⟨512,1,{0,1,7},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),3),((33/20),(33/20)),(121/256),(5/261)⟩⟩
checked_local_query query1942 := ⟨512,1,{0,2,7},.hull ⟨(1,(8/5)),((87/50),1),((113/50),3),((33/20),(33/20)),(121/195),(61/256)⟩⟩
checked_local_query query1943 := ⟨512,1,{1,2,7},.hull ⟨(1,(12/5)),((87/50),1),((47/20),(33/20)),((33/20),(33/20)),(15/28),(71/267)⟩⟩
checked_local_query query1944 := ⟨512,1,{0,3,7},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),3),((33/20),(33/20)),(121/256),(5/261)⟩⟩
checked_local_query query1945 := ⟨512,1,{1,3,7},.hull ⟨(1,(12/5)),((47/20),(33/20)),((113/50),3),((33/20),(47/20)),(151/445),(28/117)⟩⟩
checked_local_query query1946 := ⟨512,1,{2,3,7},.hull ⟨((87/50),1),((47/20),(33/20)),((113/50),3),((113/50),2),(52/61),(136/441)⟩⟩
checked_local_query query1947 := ⟨512,1,{0,4,7},.hull ⟨(1,(8/5)),((47/20),(33/20)),((113/50),3),((33/20),(33/20)),(121/256),(5/261)⟩⟩
checked_local_query query1948 := ⟨512,1,{1,4,7},.hull ⟨(1,(12/5)),((47/20),(33/20)),((113/50),3),((33/20),(47/20)),(151/445),(28/117)⟩⟩
checked_local_query query1949 := ⟨512,1,{2,4,7},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query1950 := ⟨512,1,{3,4,7},.hull ⟨((87/50),2),((47/20),(33/20)),((113/50),3),((113/50),2),(52/61),(91/396)⟩⟩
checked_local_query query1951 := ⟨512,1,{0,5,7},.hull ⟨(1,(8/5)),((113/50),1),((113/50),3),((33/20),(33/20)),(847/2067),(151/840)⟩⟩

end N12Compact.HistoricalOwnership.Queries
