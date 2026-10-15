import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query384 := ⟨2,1,{6,8,9},.hull ⟨((19/25),(187/100)),((457/500),1),(3,(8/5)),(1,(8/5)),(9/29),(2787/31787)⟩⟩
checked_local_query query385 := ⟨2,1,{7,8,9},.hull ⟨((19/25),(187/100)),((457/500),1),(3,(8/5)),(1,(8/5)),(9/29),(2787/31787)⟩⟩
checked_local_query query386 := ⟨12,1,{0},.four ⟨true,true,false⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query387 := ⟨12,1,{1},.four ⟨true,true,false⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query388 := ⟨12,1,{0,1},.hull ⟨(1,(8/5)),(3,(457/500)),(1,(12/5)),((33/20),(33/20)),(5200/10541),(5459/16000)⟩⟩
checked_local_query query389 := ⟨12,1,{2},.hull ⟨((87/50),1),((1543/500),1),((87/50),1),((113/50),1),(260/673),0⟩⟩
checked_local_query query390 := ⟨12,1,{0,2},.hull ⟨((87/50),1),((1543/500),1),((87/50),1),((113/50),1),(260/673),0⟩⟩
checked_local_query query391 := ⟨12,1,{1,2},.hull ⟨(1,(12/5)),((87/50),1),(3,(457/500)),((33/20),(33/20)),(26705/67268),(8875/42509)⟩⟩
checked_local_query query392 := ⟨12,1,{3},.four ⟨true,true,false⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query393 := ⟨12,1,{0,3},.hull ⟨(1,(8/5)),(3,(457/500)),((87/50),2),((33/20),(33/20)),(11150/38087),(27295/65382)⟩⟩
checked_local_query query394 := ⟨12,1,{1,3},.four ⟨true,true,false⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query395 := ⟨12,1,{2,3},.hull ⟨((87/50),1),((1543/500),1),((87/50),1),((113/50),1),(260/673),0⟩⟩
checked_local_query query396 := ⟨12,1,{4},.four ⟨false,true,false⟩ fourDatum9 fourDatum9_checked⟩
checked_local_query query397 := ⟨12,1,{0,4},.hull ⟨(1,(8/5)),(3,(457/500)),((87/50),3),((33/20),(33/20)),(4850/15343),(27295/165382)⟩⟩
checked_local_query query398 := ⟨12,1,{1,4},.hull ⟨(1,(12/5)),(3,(457/500)),((87/50),3),((33/20),(47/20)),(3050/10241),(6185/16426)⟩⟩
checked_local_query query399 := ⟨12,1,{2,4},.hull ⟨((87/50),1),((87/50),3),((87/50),1),((87/50),2),(1/2),0⟩⟩
checked_local_query query400 := ⟨12,1,{3,4},.hull ⟨((87/50),2),(3,(457/500)),((87/50),3),((113/50),2),(6500/8691),(2353/5250)⟩⟩
checked_local_query query401 := ⟨12,1,{0,5},.four ⟨true,true,false⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query402 := ⟨12,1,{1,5},.four ⟨true,true,false⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query403 := ⟨12,1,{2,5},.four ⟨true,true,false⟩ fourDatum0 fourDatum0_checked⟩
checked_local_query query404 := ⟨12,1,{3,5},.four ⟨true,true,false⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query405 := ⟨12,1,{4,5},.hull ⟨((87/50),3),((113/50),1),(3,(457/500)),((113/50),2),(2191/11441),(6500/17941)⟩⟩
checked_local_query query406 := ⟨12,1,{6},.four ⟨false,true,false⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query407 := ⟨12,1,{0,6},.hull ⟨(1,(8/5)),(3,(457/500)),((113/50),2),((33/20),(33/20)),(9850/55923),(27295/83218)⟩⟩
checked_local_query query408 := ⟨12,1,{1,6},.hull ⟨(1,(12/5)),(3,(457/500)),((113/50),2),((87/50),2),(200/743),(7491/26809)⟩⟩
checked_local_query query409 := ⟨12,1,{2,6},.hull ⟨((87/50),1),((1543/500),1),((87/50),1),((113/50),1),(260/673),0⟩⟩
checked_local_query query410 := ⟨12,1,{3,6},.hull ⟨((87/50),2),(3,(457/500)),((113/50),2),((47/20),(33/20)),(9100/17163),(3691/9412)⟩⟩
checked_local_query query411 := ⟨12,1,{4,6},.four ⟨false,true,false⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query412 := ⟨12,1,{5,6},.hull ⟨((113/50),1),(3,(457/500)),((113/50),2),((47/20),(33/20)),(4500/12563),(24437/37000)⟩⟩
checked_local_query query413 := ⟨12,1,{7},.four ⟨false,true,false⟩ fourDatum7 fourDatum7_checked⟩
checked_local_query query414 := ⟨12,1,{0,7},.hull ⟨(1,(8/5)),(3,(457/500)),((113/50),3),((33/20),(33/20)),(42350/155923),(27295/183218)⟩⟩
checked_local_query query415 := ⟨12,1,{1,7},.hull ⟨(1,(12/5)),(3,(457/500)),((113/50),3),((33/20),(47/20)),(22650/110323),(43295/153618)⟩⟩

end N12Compact.HistoricalOwnership.Queries
