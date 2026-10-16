import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query32 := ⟨32,0,{2,7},.hull ⟨((8/5),1),((81/25),(213/100)),((12/5),3),(2,(87/50)),(130/1009),(476/1485)⟩⟩
checked_local_query query33 := ⟨32,0,{3,7},.hull ⟨((8/5),3),((81/25),(213/100)),((1543/500),3),(3,(113/50)),(54982/64421),(220/64641)⟩⟩
checked_local_query query34 := ⟨32,0,{4,7},.hull ⟨(2,(87/50)),((81/25),(213/100)),((12/5),3),((47/20),(47/20)),(394/1573),(6199/14064)⟩⟩
checked_local_query query35 := ⟨32,0,{5,7},.hull ⟨(2,(113/50)),((81/25),(213/100)),((1543/500),3),((47/20),(47/20)),(8063/45084),(7855/52939)⟩⟩
checked_local_query query36 := ⟨32,0,{6,7},.hull ⟨((12/5),1),((81/25),(213/100)),((1543/500),3),(3,(113/50)),(16782/26221),(19020/45241)⟩⟩
checked_local_query query37 := ⟨32,0,{0,8},.hull ⟨(1,(87/50)),(3,(87/50)),(1,(87/50)),(2,(87/50)),(1/2),0⟩⟩
checked_local_query query38 := ⟨32,0,{1,8},.hull ⟨(1,(113/50)),(3,(87/50)),((1543/500),3),((33/20),(47/20)),(14663/102336),(6475/32059)⟩⟩
checked_local_query query39 := ⟨32,0,{2,8},.hull ⟨((8/5),1),(3,(87/50)),((1543/500),3),((47/20),(33/20)),(26705/67268),(8875/42509)⟩⟩
checked_local_query query40 := ⟨32,0,{3,8},.hull ⟨((8/5),3),(3,(87/50)),((81/25),(213/100)),((47/20),(47/20)),(4135/8134),(25/606)⟩⟩
checked_local_query query41 := ⟨32,0,{4,8},.hull ⟨(2,(87/50)),(3,(87/50)),((1543/500),3),(3,(113/50)),(8691/9250),(26/63)⟩⟩
checked_local_query query42 := ⟨32,0,{5,8},.hull ⟨(2,(113/50)),(3,(87/50)),((1543/500),3),((47/20),(47/20)),(8063/51636),(3400/16309)⟩⟩
checked_local_query query43 := ⟨32,0,{6,8},.hull ⟨(3,(87/50)),(3,(72/25)),(3,(87/50)),(3,(113/50)),(26/57),0⟩⟩
checked_local_query query44 := ⟨32,0,{7,8},.hull ⟨((12/5),3),(3,(87/50)),((81/25),(213/100)),(3,(113/50)),(83/187),(260/447)⟩⟩
checked_local_query query45 := ⟨32,0,{0,9},.hull ⟨(1,(87/50)),((81/25),(213/100)),((1543/500),3),(2,(113/50)),(8764/61703),(38740/100443)⟩⟩
checked_local_query query46 := ⟨32,0,{1,9},.hull ⟨(1,(113/50)),((81/25),(213/100)),((1543/500),3),((33/20),(47/20)),(14663/82134),(14305/96439)⟩⟩
checked_local_query query47 := ⟨32,0,{2,9},.hull ⟨((8/5),1),((81/25),(213/100)),((1543/500),3),((47/20),(33/20)),(26705/69116),(10925/80041)⟩⟩
checked_local_query query48 := ⟨32,0,{3,9},.hull ⟨((8/5),3),((1543/500),3),((8/5),3),((12/5),3),(400/743),0⟩⟩
checked_local_query query49 := ⟨32,0,{4,9},.four ⟨false,true,true⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query50 := ⟨32,0,{5,9},.hull ⟨(2,(113/50)),((81/25),(213/100)),((1543/500),3),((47/20),(47/20)),(8063/45084),(7855/52939)⟩⟩
checked_local_query query51 := ⟨32,0,{6,9},.hull ⟨((12/5),1),((81/25),(213/100)),((1543/500),3),((1543/500),2),(49/60),(463/6463)⟩⟩
checked_local_query query52 := ⟨32,0,{8,9},.hull ⟨(3,(87/50)),((81/25),(213/100)),((1543/500),3),((1543/500),2),(43/120),(481/4481)⟩⟩
checked_local_query query53 := ⟨192,0,{0},.hull ⟨(1,(87/50)),(1,(1543/500)),(1,(87/50)),(1,(113/50)),(260/673),0⟩⟩
checked_local_query query54 := ⟨192,0,{2},.four ⟨false,false,true⟩ fourDatum2 fourDatum2_checked⟩
checked_local_query query55 := ⟨192,0,{4},.four ⟨false,false,true⟩ fourDatum8 fourDatum8_checked⟩
checked_local_query query56 := ⟨192,0,{5},.four ⟨true,false,true⟩ fourDatum5 fourDatum5_checked⟩
checked_local_query query57 := ⟨192,0,{6},.four ⟨false,false,true⟩ fourDatum10 fourDatum10_checked⟩
checked_local_query query58 := ⟨192,0,{7},.hull ⟨((457/500),3),((12/5),3),((457/500),3),((8/5),3),(343/743),0⟩⟩
checked_local_query query59 := ⟨192,0,{8},.four ⟨true,false,true⟩ fourDatum9 fourDatum9_checked⟩
checked_local_query query60 := ⟨192,0,{9},.four ⟨true,false,true⟩ fourDatum7 fourDatum7_checked⟩
checked_local_query query61 := ⟨192,2,{1},.hull ⟨(1,(113/50)),(1,(1543/500)),(1,(113/50)),(1,(12/5)),(10/59),0⟩⟩
checked_local_query query62 := ⟨1536,0,{0},.hull ⟨(1,(87/50)),((47/20),(33/20)),((47/20),(47/20)),(2,(87/50)),(122/171),(2/21)⟩⟩
checked_local_query query63 := ⟨1536,0,{1},.hull ⟨(1,(113/50)),((47/20),(33/20)),((47/20),(47/20)),(2,(113/50)),(18/67),(122/189)⟩⟩

end N12Compact.HistoricalOwnership.Queries
