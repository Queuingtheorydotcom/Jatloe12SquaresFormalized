import Compact.HistoricalData.RowsChunks.Part000000
import Compact.HistoricalData.RowsChunks.Part001556
import Compact.HistoricalData.RowsChunks.Part003112
import Compact.HistoricalData.RowsChunks.Part004668
import Compact.HistoricalData.RowsChunks.Part006223
import Compact.HistoricalData.RowsChunks.Part007779
import Compact.HistoricalData.RowsChunks.Part009335
import Compact.HistoricalData.RowsChunks.Part010891
import Compact.HistoricalData.RowsChunks.Part012446
import Compact.HistoricalData.RowsChunks.Part014002
import Compact.HistoricalData.RowsChunks.Part015558
import Compact.HistoricalData.RowsChunks.Part017114
import Compact.HistoricalData.RowsChunks.Part018669
import Compact.HistoricalData.RowsChunks.Part020225
import Compact.HistoricalData.RowsChunks.Part021780
import Compact.HistoricalData.RowsChunks.Part023336
import Compact.HistoricalData.RowsChunks.Part024891
import Compact.HistoricalData.RowsChunks.Part026447
import Compact.HistoricalData.RowsChunks.Part028003
import Compact.HistoricalData.RowsChunks.Part029559
import Compact.HistoricalData.RowsChunks.Part031114
import Compact.HistoricalData.RowsChunks.Part032670
import Compact.HistoricalData.RowsChunks.Part034226
import Compact.HistoricalData.RowsChunks.Part035782
import Compact.HistoricalData.RowsChunks.Part037337
import Compact.HistoricalData.RowsChunks.Part038893
import Compact.HistoricalData.RowsChunks.Part040449
import Compact.HistoricalData.RowsChunks.Part042005
import Compact.HistoricalData.RowsChunks.Part043560
import Compact.HistoricalData.RowsChunks.Part045116
import Compact.HistoricalData.RowsChunks.Part046671
import Compact.HistoricalData.RowsChunks.Part048227
import Compact.HistoricalData.RowsChunks.Part049782
import Compact.HistoricalData.RowsChunks.Part051338
import Compact.HistoricalData.RowsChunks.Part052894
import Compact.HistoricalData.RowsChunks.Part054450
import Compact.HistoricalData.RowsChunks.Part056005
import Compact.HistoricalData.RowsChunks.Part057561
import Compact.HistoricalData.RowsChunks.Part059117
import Compact.HistoricalData.RowsChunks.Part060673
import Compact.HistoricalData.RowsChunks.Part062228
import Compact.HistoricalData.RowsChunks.Part063784
import Compact.HistoricalData.RowsChunks.Part065340
import Compact.HistoricalData.RowsChunks.Part066896
import Compact.HistoricalData.RowsChunks.Part068451
import Compact.HistoricalData.RowsChunks.Part070007
import Compact.HistoricalData.RowsChunks.Part071562
import Compact.HistoricalData.RowsChunks.Part073118
import Compact.HistoricalData.RowsChunks.Part074673
import Compact.HistoricalData.RowsChunks.Part076229
import Compact.HistoricalData.RowsChunks.Part077785
import Compact.HistoricalData.RowsChunks.Part079341
import Compact.HistoricalData.RowsChunks.Part080896
import Compact.HistoricalData.RowsChunks.Part082452
import Compact.HistoricalData.RowsChunks.Part084007
import Compact.HistoricalData.RowsChunks.Part088312
import Compact.HistoricalData.RowsChunks.Part092077
import Compact.HistoricalData.RowsChunks.Part095936
import Compact.HistoricalData.RowsChunks.Part099420
import Compact.HistoricalData.RowsChunks.Part103150
import Compact.HistoricalData.RowsChunks.Part106869
import Compact.HistoricalData.RowsChunks.Part109619
import Compact.HistoricalData.RowsChunks.Part111192
import Compact.HistoricalData.RowsChunks.Part112911

/-! Original global IDs, restricted to the exact direct-pruning consumer closure.
Unused IDs have the ordinary sparse fallback; no active consumer may use them.
This bank is a proposal until all replacement contracts and bindings replay. -/
namespace N12Compact.HistoricalData
open IntegerSupport
set_option Elab.async false
noncomputable def rowData : SparseLiteral.Tree (Row × Nat) :=
  (.node 49781 (⟨72575500000000,-2892600000000,-148975785516907,false⟩,72575499999999)
  (.node 24890 (⟨148853900000000,-38557700000000,-144075655447549,false⟩,148853899999999)
  (.node 12445 (⟨-763605400000000,-6110533100000000,15977305921930921,false⟩,6110533099999999)
  (.node 6222 (⟨1324274900000000,-124064000000000,-4280648771003689,false⟩,1324274899999999)
  (.node 3111 (⟨0,25000000,-69407313,false⟩,24999999)
  (.node 1555 (⟨0,50000000,-75778043,false⟩,49999999)
  RowsChunks.part000000
  RowsChunks.part001556)
  (.node 4667 (⟨-21198768750000,-20080618750000,45130631634841,false⟩,21198768749999)
  RowsChunks.part003112
  RowsChunks.part004668))
  (.node 9334 (⟨505269500000000,-2918039800000000,4565435018142467,false⟩,2918039799999999)
  (.node 7778 (⟨0,-5000000,13332757,false⟩,4999999)
  RowsChunks.part006223
  RowsChunks.part007779)
  (.node 10890 (⟨100000000,0,-221332217,false⟩,99999999)
  RowsChunks.part009335
  RowsChunks.part010891)))
  (.node 18668 (⟨0,-100000000,154822491,false⟩,99999999)
  (.node 15557 (⟨28324700000000,-6157200000000,-35423000371387,false⟩,28324699999999)
  (.node 14001 (⟨449643437500000,-10664962500000,-1055826879039089,false⟩,449643437499999)
  RowsChunks.part012446
  RowsChunks.part014002)
  (.node 17113 (⟨-500000,0,827751,false⟩,499999)
  RowsChunks.part015558
  RowsChunks.part017114))
  (.node 21779 (⟨-20000000,0,48660639,false⟩,19999999)
  (.node 20224 (⟨13902980000000,543280000000,-30739409130781,false⟩,13902979999999)
  RowsChunks.part018669
  RowsChunks.part020225)
  (.node 23335 (⟨-4000000,0,7137663,false⟩,3999999)
  RowsChunks.part021780
  RowsChunks.part023336))))
  (.node 37336 (⟨130872500000000,-378582700000000,310231089094709,false⟩,378582699999999)
  (.node 31113 (⟨0,100000000,-284079197,false⟩,99999999)
  (.node 28002 (⟨-362533400000000,-42630700000000,582921740949839,false⟩,362533399999999)
  (.node 26446 (⟨50592200000000,390867220000000,-965570264867361,false⟩,390867219999999)
  RowsChunks.part024891
  RowsChunks.part026447)
  (.node 29558 (⟨0,-25000000,38580171,false⟩,24999999)
  RowsChunks.part028003
  RowsChunks.part029559))
  (.node 34225 (⟨0,-100000000,260917077,false⟩,99999999)
  (.node 32669 (⟨100000000,0,-244700923,false⟩,99999999)
  RowsChunks.part031114
  RowsChunks.part032670)
  (.node 35781 (⟨-471922800000000,-85488700000000,1161626996023389,false⟩,471922799999999)
  RowsChunks.part034226
  RowsChunks.part035782)))
  (.node 43559 (⟨0,-50000000,122453269,false⟩,49999999)
  (.node 40448 (⟨254092400000000,560301900000000,-1789033824959261,false⟩,560301899999999)
  (.node 38892 (⟨50000000,0,-92626699,false⟩,49999999)
  RowsChunks.part037337
  RowsChunks.part038893)
  (.node 42004 (⟨-100000000,0,149560891,false⟩,99999999)
  RowsChunks.part040449
  RowsChunks.part042005))
  (.node 46670 (⟨182970750000000,2859100000000,-312818470903509,false⟩,182970749999999)
  (.node 45115 (⟨100000000,0,-280969739,false⟩,99999999)
  RowsChunks.part043560
  RowsChunks.part045116)
  (.node 48226 (⟨0,50000000,-70232571,false⟩,49999999)
  RowsChunks.part046671
  RowsChunks.part048227)))))
  (.node 74672 (⟨39380325000000,48751400000000,-179433253669021,false⟩,48751399999999)
  (.node 62227 (⟨0,4000000,-11191637,false⟩,3999999)
  (.node 56004 (⟨1541500000000,-400400000000,-3470203819799,false⟩,1541499999999)
  (.node 52893 (⟨-15437150000000,22981050000000,-32749395691441,false⟩,22981049999999)
  (.node 51337 (⟨0,-50000000,129562579,false⟩,49999999)
  RowsChunks.part049782
  RowsChunks.part051338)
  (.node 54449 (⟨100000000,0,-159036217,false⟩,99999999)
  RowsChunks.part052894
  RowsChunks.part054450))
  (.node 59116 (⟨47229975000000,105691700000000,-276297024691837,false⟩,105691699999999)
  (.node 57560 (⟨6250000,0,-15880283,false⟩,6249999)
  RowsChunks.part056005
  RowsChunks.part057561)
  (.node 60672 (⟨0,-5000000,3801101,false⟩,4999999)
  RowsChunks.part059117
  RowsChunks.part060673)))
  (.node 68450 (⟨0,100000000,-280450381,false⟩,99999999)
  (.node 65339 (⟨-548788400000000,1047471950000000,-1758852603969309,false⟩,1047471949999999)
  (.node 63783 (⟨-100000000,0,250839801,false⟩,99999999)
  RowsChunks.part062228
  RowsChunks.part063784)
  (.node 66895 (⟨40512300000000,-33281800000000,-89675452462153,false⟩,40512299999999)
  RowsChunks.part065340
  RowsChunks.part066896))
  (.node 71561 (⟨-63732845000000,-107771885000000,298849474109107,false⟩,107771884999999)
  (.node 70006 (⟨3042153750000,3607831250000,-15696402223407,false⟩,3607831249999)
  RowsChunks.part068451
  RowsChunks.part070007)
  (.node 73117 (⟨0,-100000000,184244413,false⟩,99999999)
  RowsChunks.part071562
  RowsChunks.part073118))))
  (.node 92076 (⟨239616000000,-207388000000,103745894891,true⟩,316899999999)
  (.node 80895 (⟨562892500000000,601152200000000,-2731169472683879,false⟩,601152199999999)
  (.node 77784 (⟨0,-100000000,162132967,false⟩,99999999)
  (.node 76228 (⟨162592450000000,243866100000000,-779752826681341,false⟩,243866099999999)
  RowsChunks.part074673
  RowsChunks.part076229)
  (.node 79340 (⟨0,-100000000,161824959,false⟩,99999999)
  RowsChunks.part077785
  RowsChunks.part079341))
  (.node 84006 (⟨100000000,0,-235076671,false⟩,99999999)
  (.node 82451 (⟨-50000000,0,96857643,false⟩,49999999)
  RowsChunks.part080896
  RowsChunks.part082452)
  (.node 88311 (⟨-5171200000000,5533500000000,4259702674687,true⟩,7573699999999)
  RowsChunks.part084007
  RowsChunks.part088312)))
  (.node 106868 (⟨51200000000,-6553500000000,22119529907867,true⟩,6553699999999)
  (.node 99419 (⟨-1635900000000,-128000000000,4378433439753,true⟩,1640899999999)
  (.node 95935 (⟨1664000000000,-1215900000000,787648178459,true⟩,2060899999999)
  RowsChunks.part092077
  RowsChunks.part095936)
  (.node 103149 (⟨-115200000000,1636375000000,-2352790907991,true⟩,1640424999999)
  RowsChunks.part099420
  RowsChunks.part103150))
  (.node 111191 (⟨-189900000000,-424960000000,1197664257509,true⟩,465459999999)
  (.node 109618 (⟨28485600000,70860800000,-124670932031,true⟩,76371999999)
  RowsChunks.part106869
  RowsChunks.part109619)
  (.node 112910 (⟨640000000,-40957500000,61005257907,true⟩,40962499999)
  RowsChunks.part111192
  RowsChunks.part112911))))))
noncomputable def rowPair (index : Nat) : Row × Nat :=
  SparseLiteral.lookup (⟨0,0,0,false⟩,0) rowData index
noncomputable def rows (i : Fin rowCount) : Row := (rowPair i.val).1
noncomputable def denominators (i : Fin rowCount) : Nat := (rowPair i.val).2+1
theorem positive_denominators (i : Fin rowCount) : 0 < denominators i := Nat.zero_lt_succ _
end N12Compact.HistoricalData
