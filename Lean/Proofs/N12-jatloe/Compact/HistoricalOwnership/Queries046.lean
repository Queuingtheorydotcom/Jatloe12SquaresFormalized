import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1472 := ⟨1024,1,{5,8},.hull ⟨((113/50),1),(3,(8/5)),((47/20),(47/20)),((47/20),(33/20)),(9/74),(61/135)⟩⟩
checked_local_query query1473 := ⟨1024,1,{7,8},.four ⟨true,true,true⟩ fourDatum80 fourDatum80_checked⟩
checked_local_query query1474 := ⟨1024,1,{0,9},.hull ⟨(1,(8/5)),(3,(12/5)),((47/20),(47/20)),((87/50),2),(15/212),(52/105)⟩⟩
checked_local_query query1475 := ⟨1024,1,{1,9},.four ⟨false,true,true⟩ fourDatum71 fourDatum71_checked⟩
checked_local_query query1476 := ⟨1024,1,{2,9},.hull ⟨((87/50),1),(3,(12/5)),((47/20),(47/20)),((113/50),2),(92/315),(76/121)⟩⟩
checked_local_query query1477 := ⟨1024,1,{3,9},.short ⟨⟨true,true,true⟩,.fiveRight⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨((87/50),2),((87/50),2),((87/50),2),((87/50),2),0,0⟩]⟩
checked_local_query query1478 := ⟨1024,1,{4,9},.short ⟨⟨true,true,true⟩,.fiveLeft⟩ [⟨((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),((47/20),(47/20)),0,0⟩,⟨((87/50),3),((87/50),3),((87/50),3),((87/50),3),0,0⟩]⟩
checked_local_query query1479 := ⟨1024,1,{5,9},.hull ⟨((113/50),1),(3,(12/5)),((47/20),(47/20)),((47/20),(33/20)),(9/74),(355/873)⟩⟩
checked_local_query query1480 := ⟨1024,1,{8,9},.four ⟨false,true,false⟩ fourDatum65 fourDatum65_checked⟩
checked_local_query query1481 := ⟨1024,2,{5,16,18},.four ⟨false,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1482 := ⟨1024,2,{3,5,16},.four ⟨true,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1483 := ⟨1024,2,{3,5,13,16},.four ⟨true,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1484 := ⟨1024,2,{3,5,14,16},.four ⟨true,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1485 := ⟨1024,2,{3,5,17},.hull ⟨((8/5),3),((113/50),3),((8/5),3),((87/50),3),(7/33),0⟩⟩
checked_local_query query1486 := ⟨1024,2,{3,5,13,17},.hull ⟨((8/5),3),((113/50),3),((8/5),3),((87/50),3),(7/33),0⟩⟩
checked_local_query query1487 := ⟨1024,2,{3,5,16,17},.hull ⟨((8/5),3),((113/50),3),((8/5),3),((87/50),3),(7/33),0⟩⟩
checked_local_query query1488 := ⟨1024,2,{3,5,16,18},.four ⟨false,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1489 := ⟨1024,2,{3,5,19},.four ⟨false,true,true⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1490 := ⟨1024,2,{3,5,16,19},.four ⟨false,true,true⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1491 := ⟨1024,2,{3,5,17,19},.hull ⟨((8/5),3),((113/50),3),((8/5),3),((87/50),3),(7/33),0⟩⟩
checked_local_query query1492 := ⟨1024,2,{4,5,17},.four ⟨true,true,true⟩ fourDatum77 fourDatum77_checked⟩
checked_local_query query1493 := ⟨1024,2,{4,5,13,17},.four ⟨true,true,true⟩ fourDatum77 fourDatum77_checked⟩
checked_local_query query1494 := ⟨1024,2,{4,5,14,17},.four ⟨true,true,true⟩ fourDatum77 fourDatum77_checked⟩
checked_local_query query1495 := ⟨1024,2,{4,5,16,18},.four ⟨false,true,true⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1496 := ⟨1024,2,{4,5,19},.hull ⟨(2,(87/50)),(3,(12/5)),((47/20),(47/20)),((113/50),2),(338/1453),(442/1895)⟩⟩
checked_local_query query1497 := ⟨1024,2,{4,5,17,19},.hull ⟨(2,(87/50)),(3,(12/5)),((113/50),3),((113/50),2),(13/50),(221/2721)⟩⟩
checked_local_query query1498 := ⟨1024,2,{7,13,16},.hull ⟨((87/50),2),((113/50),2),((12/5),3),(2,(113/50)),(17/74),(13/50)⟩⟩
checked_local_query query1499 := ⟨1024,2,{7,14,16},.hull ⟨((87/50),3),((12/5),3),((87/50),3),((113/50),3),(26/33),0⟩⟩
checked_local_query query1500 := ⟨1024,2,{7,13,17},.hull ⟨((87/50),2),((47/20),(47/20)),((12/5),3),(2,(113/50)),(442/1557),(338/1895)⟩⟩
checked_local_query query1501 := ⟨1024,2,{7,14,17},.four ⟨true,true,true⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query1502 := ⟨1024,2,{7,16,18},.four ⟨true,true,true⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1503 := ⟨1024,2,{5,7,14,16},.hull ⟨((87/50),3),((12/5),3),((87/50),3),((113/50),3),(26/33),0⟩⟩

end N12Compact.HistoricalOwnership.Queries
