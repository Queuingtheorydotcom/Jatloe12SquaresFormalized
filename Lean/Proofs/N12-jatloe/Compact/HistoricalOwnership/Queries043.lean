import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1376 := ⟨32768,1,{2,8,9},.hull ⟨((87/50),1),(3,(8/5)),(2,(1543/500)),((113/50),2),(20618/38109),(7900/20603)⟩⟩
checked_local_query query1377 := ⟨32768,1,{3,8,9},.hull ⟨((87/50),2),(3,(8/5)),(3,(12/5)),((113/50),2),(13/50),(13/63)⟩⟩
checked_local_query query1378 := ⟨32768,1,{4,8,9},.hull ⟨((87/50),3),(3,(8/5)),(3,(12/5)),((47/20),(47/20)),(453/973),(5/144)⟩⟩
checked_local_query query1379 := ⟨32768,1,{5,8,9},.hull ⟨(2,(1543/500)),((113/50),1),(3,(8/5)),((113/50),2),(17491/35991),(6500/42491)⟩⟩
checked_local_query query1380 := ⟨32768,1,{6,8,9},.hull ⟨(2,(1543/500)),((113/50),2),(3,(8/5)),((47/20),(47/20)),(2159/5109),(9437/34982)⟩⟩
checked_local_query query1381 := ⟨32768,1,{7,8,9},.four ⟨true,true,true⟩ fourDatum27 fourDatum27_checked⟩
checked_local_query query1382 := ⟨32768,2,{3,14,17,19},.four ⟨true,false,true⟩ fourDatum16 fourDatum16_checked⟩
checked_local_query query1383 := ⟨32768,2,{5,11,14,17},.hull ⟨(1,(12/5)),(2,(113/50)),((113/50),3),((33/20),(47/20)),(2265/3677),(205/3882)⟩⟩
checked_local_query query1384 := ⟨32768,2,{5,14,17,19},.hull ⟨((87/50),3),(2,(113/50)),(3,(12/5)),((47/20),(47/20)),(453/494),(706/1941)⟩⟩
checked_local_query query1385 := ⟨32768,2,{7,11,14,17},.four ⟨true,true,true⟩ fourDatum16 fourDatum16_checked⟩
checked_local_query query1386 := ⟨12,2,{8,15},.hull ⟨((113/50),1),((1543/500),1),((113/50),1),((12/5),1),(10/59),0⟩⟩
checked_local_query query1387 := ⟨48,0,{0},.four ⟨true,true,true⟩ fourDatum9 fourDatum9_checked⟩
checked_local_query query1388 := ⟨48,0,{1},.four ⟨true,true,true⟩ fourDatum7 fourDatum7_checked⟩
checked_local_query query1389 := ⟨48,0,{2},.four ⟨false,true,true⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query1390 := ⟨48,0,{3},.hull ⟨((8/5),3),((1543/500),3),((8/5),3),((12/5),3),(400/743),0⟩⟩
checked_local_query query1391 := ⟨48,0,{4},.four ⟨false,true,true⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query1392 := ⟨48,0,{5},.four ⟨true,true,true⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query1393 := ⟨48,0,{6},.four ⟨false,true,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query1394 := ⟨48,0,{8},.hull ⟨(3,(87/50)),(3,(1543/500)),(3,(87/50)),(3,(113/50)),(260/673),0⟩⟩
checked_local_query query1395 := ⟨48,1,{0},.four ⟨true,true,true⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query1396 := ⟨48,1,{1},.four ⟨true,true,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query1397 := ⟨48,1,{2},.four ⟨false,true,true⟩ fourDatum9 fourDatum9_checked⟩
checked_local_query query1398 := ⟨48,1,{3},.four ⟨true,true,true⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query1399 := ⟨48,1,{4},.hull ⟨((87/50),3),((1543/500),3),((87/50),3),((113/50),3),(260/673),0⟩⟩
checked_local_query query1400 := ⟨48,1,{5},.four ⟨false,true,true⟩ fourDatum7 fourDatum7_checked⟩
checked_local_query query1401 := ⟨48,1,{6},.four ⟨false,true,true⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query1402 := ⟨48,1,{8},.hull ⟨(3,(8/5)),(3,(1543/500)),(3,(8/5)),(3,(12/5)),(400/743),0⟩⟩
checked_local_query query1403 := ⟨48,2,{17},.hull ⟨((113/50),3),((1543/500),3),((113/50),3),((12/5),3),(10/59),0⟩⟩
checked_local_query query1404 := ⟨48,2,{9},.hull ⟨(3,(113/50)),(3,(1543/500)),(3,(113/50)),(3,(12/5)),(10/59),0⟩⟩
checked_local_query query1405 := ⟨48,2,{9,17},.hull ⟨((113/50),3),((1543/500),3),((113/50),3),((12/5),3),(10/59),0⟩⟩
checked_local_query query1406 := ⟨192,2,{1,14},.hull ⟨(1,(113/50)),(1,(1543/500)),(1,(113/50)),(1,(12/5)),(10/59),0⟩⟩
checked_local_query query1407 := ⟨1024,0,{0,1},.hull ⟨(1,(87/50)),((47/20),(47/20)),(1,(113/50)),(2,(113/50)),(52/61),(46/351)⟩⟩

end N12Compact.HistoricalOwnership.Queries
