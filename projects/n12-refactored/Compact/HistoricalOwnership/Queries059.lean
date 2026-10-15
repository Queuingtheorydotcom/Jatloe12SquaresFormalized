import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1888 := ⟨256,2,{0,5,10,12,15},.hull ⟨(1,(8/5)),((87/50),1),(2,(113/50)),((87/50),2),(17/67),(1850/2721)⟩⟩
checked_local_query query1889 := ⟨256,2,{0,5,10,13,15},.hull ⟨(1,(8/5)),((113/50),1),(2,(113/50)),(2,(87/50)),(50/63),(647/1193)⟩⟩
checked_local_query query1890 := ⟨256,2,{0,5,12,13,15},.hull ⟨(1,(87/50)),((113/50),1),(2,(113/50)),(2,(87/50)),(50/63),(925/1744)⟩⟩
checked_local_query query1891 := ⟨256,2,{0,5,10,12,16},.hull ⟨(1,(8/5)),((87/50),1),(2,(113/50)),((87/50),2),(17/67),(1850/2721)⟩⟩
checked_local_query query1892 := ⟨256,2,{0,5,10,13,16},.four ⟨false,false,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query1893 := ⟨256,2,{0,5,12,13,16},.hull ⟨(1,(87/50)),((87/50),1),((113/50),2),(2,(87/50)),(25/37),(25/38)⟩⟩
checked_local_query query1894 := ⟨256,2,{0,5,12,15,16},.hull ⟨(1,(87/50)),((87/50),1),(2,(113/50)),((87/50),2),(12/37),(25/38)⟩⟩
checked_local_query query1895 := ⟨256,2,{0,5,13,15,16},.hull ⟨(1,(87/50)),((113/50),1),((113/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query1896 := ⟨256,2,{4,5,10,11,13},.hull ⟨(1,(8/5)),(1,(12/5)),(1,(8/5)),(1,(87/50)),(7/40),0⟩⟩
checked_local_query query1897 := ⟨256,2,{4,5,10,12,15},.hull ⟨(1,(8/5)),((87/50),1),(2,(113/50)),((87/50),2),(17/67),(1850/2721)⟩⟩
checked_local_query query1898 := ⟨256,2,{4,5,10,12,16},.hull ⟨(1,(8/5)),((87/50),1),(2,(113/50)),((87/50),2),(17/67),(1850/2721)⟩⟩
checked_local_query query1899 := ⟨256,2,{4,5,12,15,16},.four ⟨true,false,false⟩ fourDatum77 fourDatum77_checked⟩
checked_local_query query1900 := ⟨256,2,{4,6,10,11,13},.hull ⟨(1,(8/5)),(1,(12/5)),(1,(8/5)),(1,(87/50)),(7/40),0⟩⟩
checked_local_query query1901 := ⟨256,2,{4,6,10,12,13},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query1902 := ⟨256,2,{4,6,10,12,15},.four ⟨false,false,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1903 := ⟨256,2,{4,6,10,13,15},.four ⟨false,false,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1904 := ⟨256,2,{4,6,12,13,15},.four ⟨true,false,false⟩ fourDatum109 fourDatum109_checked⟩
checked_local_query query1905 := ⟨256,2,{4,6,10,12,16},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query1906 := ⟨256,2,{4,6,10,13,16},.four ⟨false,false,false⟩ fourDatum70 fourDatum70_checked⟩
checked_local_query query1907 := ⟨256,2,{4,6,12,13,16},.hull ⟨((87/50),1),((12/5),1),((87/50),1),((113/50),1),(26/33),0⟩⟩
checked_local_query query1908 := ⟨256,2,{4,6,12,15,16},.four ⟨true,false,false⟩ fourDatum110 fourDatum110_checked⟩
checked_local_query query1909 := ⟨256,2,{4,6,13,15,16},.four ⟨true,false,false⟩ fourDatum93 fourDatum93_checked⟩
checked_local_query query1910 := ⟨512,1,{0,1,2},.hull ⟨(1,(8/5)),((47/20),(33/20)),(1,(12/5)),((33/20),(33/20)),(104/209),(7/216)⟩⟩
checked_local_query query1911 := ⟨512,1,{0,1,3},.hull ⟨(1,(8/5)),((47/20),(33/20)),((87/50),2),((33/20),(33/20)),(223/468),(35/503)⟩⟩
checked_local_query query1912 := ⟨512,1,{0,2,3},.hull ⟨(1,(8/5)),((87/50),1),((87/50),2),((33/20),(33/20)),(223/313),(427/740)⟩⟩
checked_local_query query1913 := ⟨512,1,{1,2,3},.hull ⟨(1,(12/5)),((87/50),1),((47/20),(33/20)),((33/20),(33/20)),(15/28),(71/267)⟩⟩
checked_local_query query1914 := ⟨512,1,{0,1,4},.hull ⟨(1,(8/5)),((47/20),(33/20)),((87/50),3),((33/20),(33/20)),(97/202),(35/1853)⟩⟩
checked_local_query query1915 := ⟨512,1,{0,2,4},.hull ⟨(1,(8/5)),((87/50),1),((87/50),3),((33/20),(33/20)),(97/117),(427/1480)⟩⟩
checked_local_query query1916 := ⟨512,1,{1,2,4},.hull ⟨(1,(12/5)),((87/50),1),((47/20),(33/20)),((33/20),(33/20)),(15/28),(71/267)⟩⟩
checked_local_query query1917 := ⟨512,1,{0,3,4},.hull ⟨(1,(8/5)),((47/20),(33/20)),((87/50),3),((33/20),(33/20)),(97/202),(35/1853)⟩⟩
checked_local_query query1918 := ⟨512,1,{1,3,4},.hull ⟨(1,(12/5)),((47/20),(33/20)),((87/50),3),((33/20),(47/20)),(61/135),(4/13)⟩⟩
checked_local_query query1919 := ⟨512,1,{2,3,4},.short ⟨⟨true,true,false⟩,.fiveLeft⟩ [⟨((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),((47/20),(33/20)),0,0⟩,⟨((87/50),1),((87/50),1),((87/50),1),((87/50),1),0,0⟩]⟩

end N12Compact.HistoricalOwnership.Queries
