import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query0 := ⟨12,0,{0},.four ⟨true,true,false⟩ fourDatum7 fourDatum7_checked⟩
checked_local_query query1 := ⟨12,0,{1},.four ⟨true,true,false⟩ fourDatum9 fourDatum9_checked⟩
checked_local_query query2 := ⟨12,0,{2},.hull ⟨((8/5),1),((1543/500),1),((8/5),1),((12/5),1),(400/743),0⟩⟩
checked_local_query query3 := ⟨12,0,{3},.four ⟨false,true,false⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query4 := ⟨12,0,{4},.four ⟨true,true,false⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query5 := ⟨12,0,{5},.four ⟨false,true,false⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query6 := ⟨12,0,{7},.four ⟨false,true,false⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query7 := ⟨12,0,{9},.hull ⟨(3,(457/500)),(3,(113/50)),(3,(457/500)),(3,(87/50)),(413/673),0⟩⟩
checked_local_query query8 := ⟨12,2,{8},.hull ⟨(3,(457/500)),(3,(87/50)),(3,(457/500)),(3,(8/5)),(49/59),0⟩⟩
checked_local_query query9 := ⟨32,0,{0,1},.hull ⟨(1,(87/50)),((1543/500),3),(1,(113/50)),((33/20),(47/20)),(16900/31563),(3239/7748)⟩⟩
checked_local_query query10 := ⟨32,0,{0,2},.hull ⟨(1,(87/50)),((8/5),1),((81/25),(213/100)),((33/20),(33/20)),(1517/4882),(2135/9458)⟩⟩
checked_local_query query11 := ⟨32,0,{1,2},.hull ⟨(1,(113/50)),((8/5),1),((81/25),(213/100)),((33/20),(33/20)),(4273/7638),(755/4574)⟩⟩
checked_local_query query12 := ⟨32,0,{0,3},.hull ⟨(1,(87/50)),((81/25),(213/100)),((8/5),3),((33/20),(47/20)),(906/2951),(11129/25884)⟩⟩
checked_local_query query13 := ⟨32,0,{1,3},.hull ⟨(1,(113/50)),((81/25),(213/100)),((1543/500),3),((33/20),(47/20)),(14663/82134),(14305/96439)⟩⟩
checked_local_query query14 := ⟨32,0,{2,3},.hull ⟨((8/5),1),((81/25),(213/100)),((8/5),3),((33/20),(33/20)),(200/4541),(2019/6560)⟩⟩
checked_local_query query15 := ⟨32,0,{0,4},.hull ⟨(1,(87/50)),(2,(87/50)),((1543/500),3),(2,(113/50)),(2191/9250),(26/63)⟩⟩
checked_local_query query16 := ⟨32,0,{1,4},.hull ⟨(1,(113/50)),(2,(87/50)),((1543/500),3),((33/20),(47/20)),(14663/69836),(5350/22809)⟩⟩
checked_local_query query17 := ⟨32,0,{2,4},.hull ⟨((8/5),1),((81/25),(213/100)),((1543/500),3),((47/20),(33/20)),(26705/69116),(10925/80041)⟩⟩
checked_local_query query18 := ⟨32,0,{3,4},.hull ⟨((8/5),3),(2,(87/50)),((81/25),(213/100)),(2,(113/50)),(541/944),(65/537)⟩⟩
checked_local_query query19 := ⟨32,0,{0,5},.hull ⟨(1,(87/50)),((81/25),(213/100)),((1543/500),3),((47/20),(47/20)),(21427/58448),(41995/100443)⟩⟩
checked_local_query query20 := ⟨32,0,{1,5},.hull ⟨(1,(113/50)),((81/25),(213/100)),((1543/500),3),((33/20),(47/20)),(14663/82134),(14305/96439)⟩⟩
checked_local_query query21 := ⟨32,0,{2,5},.hull ⟨((8/5),1),((81/25),(213/100)),(2,(113/50)),(2,(87/50)),(10/41),(476/1009)⟩⟩
checked_local_query query22 := ⟨32,0,{3,5},.hull ⟨((8/5),3),(2,(113/50)),((81/25),(213/100)),((47/20),(47/20)),(4135/5706),(1475/4328)⟩⟩
checked_local_query query23 := ⟨32,0,{4,5},.hull ⟨(2,(87/50)),((1543/500),3),(2,(113/50)),((47/20),(47/20)),(9100/17163),(3691/9412)⟩⟩
checked_local_query query24 := ⟨32,0,{0,6},.hull ⟨(1,(87/50)),((12/5),1),((81/25),(213/100)),((33/20),(33/20)),(1517/6162),(1775/11018)⟩⟩
checked_local_query query25 := ⟨32,0,{1,6},.hull ⟨(1,(113/50)),((12/5),1),((1543/500),3),((33/20),(47/20)),(14663/135968),(3375/13087)⟩⟩
checked_local_query query26 := ⟨32,0,{2,6},.hull ⟨((8/5),1),((12/5),1),((1543/500),3),((47/20),(33/20)),(5341/10800),(13/40)⟩⟩
checked_local_query query27 := ⟨32,0,{3,6},.hull ⟨((8/5),3),((12/5),1),((81/25),(213/100)),(2,(113/50)),(541/1485),(26/323)⟩⟩
checked_local_query query28 := ⟨32,0,{4,6},.hull ⟨(2,(87/50)),((12/5),1),((81/25),(213/100)),((47/20),(33/20)),(2481/8506),(1115/5368)⟩⟩
checked_local_query query29 := ⟨32,0,{5,6},.hull ⟨(2,(113/50)),((12/5),1),((81/25),(213/100)),((47/20),(33/20)),(7109/13134),(985/7552)⟩⟩
checked_local_query query30 := ⟨32,0,{0,7},.hull ⟨(1,(87/50)),((81/25),(213/100)),((1543/500),3),(2,(113/50)),(8764/61703),(38740/100443)⟩⟩
checked_local_query query31 := ⟨32,0,{1,7},.hull ⟨(1,(113/50)),((81/25),(213/100)),((1543/500),3),((33/20),(47/20)),(14663/82134),(14305/96439)⟩⟩

end N12Compact.HistoricalOwnership.Queries
