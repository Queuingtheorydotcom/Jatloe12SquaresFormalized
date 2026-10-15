import Compact.Bridge.SharedLocalQueries

namespace N12Compact.HistoricalOwnership.Queries
open S12 S12Pilot
set_option Elab.async false

checked_local_query query1824 := ⟨256,1,{5,6,9},.hull ⟨((33/20),(33/20)),((113/50),1),(3,(12/5)),((47/20),(33/20)),(105/176),(91/267)⟩⟩
checked_local_query query1825 := ⟨256,1,{0,7,9},.hull ⟨(1,(8/5)),((33/20),(33/20)),((113/50),3),((87/50),2),(133/156),(223/847)⟩⟩
checked_local_query query1826 := ⟨256,1,{1,7,9},.hull ⟨(1,(12/5)),((33/20),(33/20)),(3,(12/5)),((33/20),(47/20)),(20/209),(91/300)⟩⟩
checked_local_query query1827 := ⟨256,1,{2,7,9},.hull ⟨((33/20),(33/20)),(3,(12/5)),((113/50),3),((113/50),2),(61/135),(1/91)⟩⟩
checked_local_query query1828 := ⟨256,1,{3,7,9},.hull ⟨((33/20),(33/20)),(3,(12/5)),((113/50),3),((113/50),2),(61/135),(1/91)⟩⟩
checked_local_query query1829 := ⟨256,1,{4,7,9},.hull ⟨((33/20),(33/20)),(3,(12/5)),((87/50),3),((87/50),2),(1/15),(3/13)⟩⟩
checked_local_query query1830 := ⟨256,1,{5,7,9},.hull ⟨((113/50),1),((113/50),3),((113/50),1),((113/50),2),(1/2),0⟩⟩
checked_local_query query1831 := ⟨256,1,{6,7,9},.hull ⟨((33/20),(33/20)),(3,(12/5)),((113/50),3),((47/20),(47/20)),(74/135),(4/13)⟩⟩
checked_local_query query1832 := ⟨256,1,{0,8,9},.hull ⟨(1,(8/5)),(3,(8/5)),(3,(12/5)),((113/50),2),(13/50),(1/2)⟩⟩
checked_local_query query1833 := ⟨256,1,{1,8,9},.hull ⟨(1,(12/5)),((33/20),(33/20)),(3,(12/5)),((33/20),(47/20)),(20/209),(91/300)⟩⟩
checked_local_query query1834 := ⟨256,1,{2,8,9},.hull ⟨((33/20),(33/20)),(3,(8/5)),(3,(12/5)),((47/20),(33/20)),(105/209),(7/216)⟩⟩
checked_local_query query1835 := ⟨256,1,{3,8,9},.hull ⟨((33/20),(33/20)),(3,(12/5)),((87/50),2),((113/50),2),(7/15),(1/27)⟩⟩
checked_local_query query1836 := ⟨256,1,{4,8,9},.hull ⟨((33/20),(33/20)),(3,(8/5)),((87/50),3),((87/50),2),(1/15),(53/203)⟩⟩
checked_local_query query1837 := ⟨256,1,{5,8,9},.hull ⟨((33/20),(33/20)),((113/50),1),(3,(12/5)),((47/20),(33/20)),(105/176),(91/267)⟩⟩
checked_local_query query1838 := ⟨256,1,{6,8,9},.hull ⟨((33/20),(33/20)),(3,(8/5)),(3,(12/5)),((47/20),(33/20)),(105/209),(7/216)⟩⟩
checked_local_query query1839 := ⟨256,1,{7,8,9},.hull ⟨((33/20),(33/20)),(3,(8/5)),((113/50),3),((113/50),2),(61/135),(503/1853)⟩⟩
checked_local_query query1840 := ⟨256,2,{0,10,11,13},.hull ⟨(1,(8/5)),(1,(12/5)),(1,(8/5)),(1,(113/50)),(33/40),0⟩⟩
checked_local_query query1841 := ⟨256,2,{0,10,12,15},.four ⟨false,false,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query1842 := ⟨256,2,{0,10,13,15},.four ⟨false,false,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query1843 := ⟨256,2,{0,12,13,15},.four ⟨true,false,false⟩ fourDatum73 fourDatum73_checked⟩
checked_local_query query1844 := ⟨256,2,{0,10,12,16},.hull ⟨(1,(8/5)),((87/50),1),((113/50),2),(2,(87/50)),(43/67),(1759/2630)⟩⟩
checked_local_query query1845 := ⟨256,2,{0,10,13,16},.four ⟨false,false,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query1846 := ⟨256,2,{0,12,13,16},.hull ⟨(1,(87/50)),((87/50),1),((113/50),2),(2,(87/50)),(25/37),(25/38)⟩⟩
checked_local_query query1847 := ⟨256,2,{0,12,15,16},.hull ⟨(1,(87/50)),((87/50),1),((113/50),2),(2,(87/50)),(25/37),(25/38)⟩⟩
checked_local_query query1848 := ⟨256,2,{0,13,15,16},.hull ⟨(1,(87/50)),((113/50),1),((113/50),2),(2,(87/50)),(1/2),(37/63)⟩⟩
checked_local_query query1849 := ⟨256,2,{0,1,10,12,15},.four ⟨false,false,false⟩ fourDatum64 fourDatum64_checked⟩
checked_local_query query1850 := ⟨256,2,{0,1,10,13,15},.four ⟨false,false,false⟩ fourDatum66 fourDatum66_checked⟩
checked_local_query query1851 := ⟨256,2,{0,1,12,13,15},.four ⟨true,false,false⟩ fourDatum73 fourDatum73_checked⟩
checked_local_query query1852 := ⟨256,2,{0,1,10,12,16},.hull ⟨(1,(8/5)),((113/50),2),(1,(113/50)),((87/50),2),(1221/1559),(520/2079)⟩⟩
checked_local_query query1853 := ⟨256,2,{0,1,10,13,16},.four ⟨false,false,false⟩ fourDatum68 fourDatum68_checked⟩
checked_local_query query1854 := ⟨256,2,{0,1,12,13,16},.hull ⟨(1,(87/50)),((87/50),1),((113/50),2),(2,(87/50)),(25/37),(25/38)⟩⟩
checked_local_query query1855 := ⟨256,2,{0,1,12,15,16},.hull ⟨(1,(87/50)),((113/50),2),(1,(113/50)),((87/50),2),(37/50),(13/63)⟩⟩

end N12Compact.HistoricalOwnership.Queries
