import Compact.Cases.C898.FusedContextSyntax
import Compact.Cases.C898.CachedPairs.CyclicDirections

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

checked_c898_fan route64 commonRaw64 :=
  ⟨1196,blockRows 5,11⟩ using c898_entries%(#[
  ⟨0,15706,19707,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15706) (rows 19707)⟩,
  ⟨65,15704,19707,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15704) (rows 19707)⟩,
  ⟨66,15703,19706,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15703) (rows 19706)⟩,
  ⟨67,19704,19705,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 19704) (rows 19705)⟩,
  ⟨75,15704,19704,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15704) (rows 19704)⟩,
  ⟨139,15704,15705,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15704) (rows 15705)⟩,
  ⟨192,15705,15706,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15705) (rows 15706)⟩,
  ⟨204,15706,19707,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15706) (rows 19707)⟩,
])

checked_c898_fan route65 commonRaw65 :=
  ⟨1197,blockRows 6,12⟩ using c898_entries%(#[
  ⟨0,15713,19723,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15713) (rows 19723)⟩,
  ⟨65,15711,19723,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15711) (rows 19723)⟩,
  ⟨66,15710,19722,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15710) (rows 19722)⟩,
  ⟨67,19720,19721,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 19720) (rows 19721)⟩,
  ⟨76,15711,19720,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15711) (rows 19720)⟩,
  ⟨141,15711,15712,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15711) (rows 15712)⟩,
  ⟨192,15712,15713,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15712) (rows 15713)⟩,
  ⟨204,15713,19723,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15713) (rows 19723)⟩,
])

checked_c898_fan route66 commonRaw66 :=
  ⟨1198,blockRows 7,13⟩ using c898_cycle%(cyclicDirections,[15721,19738,19737,19736,15716,15718,15719,15720])

checked_c898_fan route67 commonRaw67 :=
  ⟨1199,blockRows 8,14⟩ using c898_cycle%(cyclicDirections,[15728,19749,19748,15723,15725,15726,15727])

checked_c898_fan route68 commonRaw68 :=
  ⟨1200,blockRows 9,15⟩ using c898_entries%(#[
  ⟨0,15734,19758,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15734) (rows 19758)⟩,
  ⟨64,15729,19758,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15729) (rows 19758)⟩,
  ⟨65,15732,19758,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15732) (rows 19758)⟩,
  ⟨144,15732,15733,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15732) (rows 15733)⟩,
  ⟨192,15733,15734,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15733) (rows 15734)⟩,
])

checked_c898_fan route69 commonRaw69 :=
  ⟨1201,blockRows 10,16⟩ using c898_entries%(#[
  ⟨0,15740,19767,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15740) (rows 19767)⟩,
  ⟨64,15735,19767,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15735) (rows 19767)⟩,
  ⟨65,15738,19767,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15738) (rows 19767)⟩,
  ⟨145,15738,15739,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15738) (rows 15739)⟩,
  ⟨192,15739,15740,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15739) (rows 15740)⟩,
])

checked_c898_fan route70 commonRaw70 :=
  ⟨1202,blockRows 11,17⟩ using c898_entries%(#[
  ⟨0,15746,19776,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15746) (rows 19776)⟩,
  ⟨64,15741,19776,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15741) (rows 19776)⟩,
  ⟨65,15743,19776,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15743) (rows 19776)⟩,
  ⟨128,15743,15745,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15743) (rows 15745)⟩,
  ⟨129,15744,19776,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15744) (rows 19776)⟩,
  ⟨145,15744,15745,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15744) (rows 15745)⟩,
  ⟨192,15745,15746,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15745) (rows 15746)⟩,
])

checked_c898_fan route71 commonRaw71 :=
  ⟨1203,blockRows 12,18⟩ using c898_entries%(#[
  ⟨0,15752,19784,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15752) (rows 19784)⟩,
  ⟨64,15747,19784,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15747) (rows 19784)⟩,
  ⟨65,15749,19784,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15749) (rows 19784)⟩,
  ⟨83,15748,15751,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15748) (rows 15751)⟩,
  ⟨84,15749,19784,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15749) (rows 19784)⟩,
  ⟨128,15749,15751,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15749) (rows 15751)⟩,
  ⟨130,15750,19784,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15750) (rows 19784)⟩,
  ⟨147,15750,15751,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15750) (rows 15751)⟩,
  ⟨192,15751,15752,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15751) (rows 15752)⟩,
])

checked_c898_fan route72 commonRaw72 :=
  ⟨1204,blockRows 13,19⟩ using c898_entries%(#[
  ⟨0,15758,19792,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15758) (rows 19792)⟩,
  ⟨64,15753,19792,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15753) (rows 19792)⟩,
  ⟨65,15755,19792,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15755) (rows 19792)⟩,
  ⟨83,15754,15757,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15754) (rows 15757)⟩,
  ⟨87,15755,19792,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15755) (rows 19792)⟩,
  ⟨128,15755,15757,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15755) (rows 15757)⟩,
  ⟨132,15756,19792,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15756) (rows 19792)⟩,
  ⟨147,15756,15757,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15756) (rows 15757)⟩,
  ⟨192,15757,15758,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15757) (rows 15758)⟩,
])

checked_c898_fan route73 commonRaw73 :=
  ⟨1205,blockRows 14,20⟩ using c898_cycle%(cyclicDirections,[15764,19801,19800,15760,15761,15762,15763])

checked_c898_fan route74 commonRaw74 :=
  ⟨1206,blockRows 15,21⟩ using c898_cycle%(cyclicDirections,[15770,19812,19811,19810,15766,15767,15768,15769])

checked_c898_fan route75 commonRaw75 :=
  ⟨1207,blockRows 16,22⟩ using c898_cycle%(cyclicDirections,[15776,19823,19822,15772,15773,15774,15775])

checked_c898_fan route76 commonRaw76 :=
  ⟨1208,blockRows 17,23⟩ using c898_cycle%(cyclicDirections,[15782,19833,19832,15778,15779,15780,15781])

checked_c898_fan route77 commonRaw77 :=
  ⟨1209,blockRows 18,24⟩ using c898_cycle%(cyclicDirections,[15788,19843,19842,15784,15785,15786,15787])

checked_c898_fan route78 commonRaw78 :=
  ⟨1210,blockRows 19,25⟩ using c898_cycle%(cyclicDirections,[15794,19853,19852,15790,15791,15792,15793])

checked_c898_fan route79 commonRaw79 :=
  ⟨1211,blockRows 20,26⟩ using c898_cycle%(cyclicDirections,[15800,19863,19862,15796,15797,15798,15799])

checked_c898_fan route80 commonRaw80 :=
  ⟨1212,blockRows 21,27⟩ using c898_cycle%(cyclicDirections,[15806,19873,19872,15802,15803,15804,15805])

checked_c898_fan route81 commonRaw81 :=
  ⟨1213,blockRows 22,28⟩ using c898_cycle%(cyclicDirections,[15812,19883,19882,15808,15809,15810,15811])

checked_c898_fan route82 commonRaw82 :=
  ⟨1214,blockRows 23,29⟩ using c898_cycle%(cyclicDirections,[15818,19893,19892,15814,15815,15816,15817])

checked_c898_fan route83 commonRaw83 :=
  ⟨1215,blockRows 24,30⟩ using c898_cycle%(cyclicDirections,[15824,19903,19902,15820,15821,15822,15823])

checked_c898_fan route84 commonRaw84 :=
  ⟨1216,blockRows 25,31⟩ using c898_cycle%(cyclicDirections,[15830,19913,19912,15826,15827,15828,15829])

checked_c898_fan route85 commonRaw85 :=
  ⟨1217,blockRows 26,32⟩ using c898_cycle%(cyclicDirections,[15836,19923,19922,15832,15833,15834,15835])

checked_c898_fan route86 commonRaw86 :=
  ⟨1218,blockRows 27,33⟩ using c898_cycle%(cyclicDirections,[15842,19933,19932,15838,15839,15840,15841])

checked_c898_fan route87 commonRaw87 :=
  ⟨1219,blockRows 28,34⟩ using c898_cycle%(cyclicDirections,[15848,19944,19943,19942,15844,15846,15847])

checked_c898_fan route88 commonRaw88 :=
  ⟨1220,blockRows 29,35⟩ using c898_cycle%(cyclicDirections,[15854,19956,19955,19954,15850,15851,15852,15853])

checked_c898_fan route89 commonRaw89 :=
  ⟨1221,blockRows 30,36⟩ using c898_cycle%(cyclicDirections,[15860,19968,19967,19966,15856,15857,15858,15859])

checked_c898_fan route90 commonRaw90 :=
  ⟨1222,blockRows 31,37⟩ using c898_cycle%(cyclicDirections,[15866,19980,19979,19978,15862,15863,15864,15865])

checked_c898_fan route91 commonRaw91 :=
  ⟨1223,blockRows 32,38⟩ using c898_cycle%(cyclicDirections,[15872,19992,19991,19990,15868,15869,15870,15871])

checked_c898_fan route92 commonRaw92 :=
  ⟨1224,blockRows 33,39⟩ using c898_cycle%(cyclicDirections,[15878,20003,20002,15874,15875,15876,15877])

checked_c898_fan route93 commonRaw93 :=
  ⟨1225,blockRows 34,40⟩ using c898_entries%(#[
  ⟨0,15884,20012,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15884) (rows 20012)⟩,
  ⟨40,15879,20012,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15879) (rows 20012)⟩,
  ⟨41,15880,20012,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15880) (rows 20012)⟩,
  ⟨105,15880,15882,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15880) (rows 15882)⟩,
  ⟨168,15882,15883,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15882) (rows 15883)⟩,
  ⟨192,15883,15884,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15883) (rows 15884)⟩,
])

checked_c898_fan route94 commonRaw94 :=
  ⟨1226,blockRows 35,41⟩ using c898_entries%(#[
  ⟨0,15891,20020,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15891) (rows 20020)⟩,
  ⟨41,15885,20020,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15885) (rows 20020)⟩,
  ⟨42,15887,20020,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15887) (rows 20020)⟩,
  ⟨106,15887,15889,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15887) (rows 15889)⟩,
  ⟨128,15888,15889,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15888) (rows 15889)⟩,
  ⟨169,15889,15890,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15889) (rows 15890)⟩,
  ⟨192,15890,15891,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15890) (rows 15891)⟩,
])

checked_c898_fan route95 commonRaw95 :=
  ⟨1227,blockRows 36,42⟩ using c898_entries%(#[
  ⟨0,15898,20029,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15898) (rows 20029)⟩,
  ⟨42,15892,20029,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15892) (rows 20029)⟩,
  ⟨43,15894,20029,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15894) (rows 20029)⟩,
  ⟨106,15894,15896,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15894) (rows 15896)⟩,
  ⟨128,15895,15896,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15895) (rows 15896)⟩,
  ⟨171,15896,15897,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15896) (rows 15897)⟩,
  ⟨192,15897,15898,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15897) (rows 15898)⟩,
])

checked_c898_fan route96 commonRaw96 :=
  ⟨1228,blockRows 37,43⟩ using c898_entries%(#[
  ⟨0,15905,20038,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15905) (rows 20038)⟩,
  ⟨43,15899,20038,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15899) (rows 20038)⟩,
  ⟨44,15901,20038,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15901) (rows 20038)⟩,
  ⟨108,15901,15903,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15901) (rows 15903)⟩,
  ⟨128,15902,15903,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15902) (rows 15903)⟩,
  ⟨172,15903,15904,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15903) (rows 15904)⟩,
  ⟨192,15904,15905,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15904) (rows 15905)⟩,
])

checked_c898_fan route97 commonRaw97 :=
  ⟨1229,blockRows 38,44⟩ using c898_entries%(#[
  ⟨0,15912,20047,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15912) (rows 20047)⟩,
  ⟨44,15906,20047,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15906) (rows 20047)⟩,
  ⟨45,15908,20047,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15908) (rows 20047)⟩,
  ⟨109,15908,15910,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15908) (rows 15910)⟩,
  ⟨128,15909,15910,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15909) (rows 15910)⟩,
  ⟨172,15910,15911,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15910) (rows 15911)⟩,
  ⟨192,15911,15912,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15911) (rows 15912)⟩,
])

checked_c898_fan route98 commonRaw98 :=
  ⟨1230,blockRows 39,45⟩ using c898_entries%(#[
  ⟨0,15920,20056,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15920) (rows 20056)⟩,
  ⟨45,15913,20056,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15913) (rows 20056)⟩,
  ⟨46,15915,20056,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15915) (rows 20056)⟩,
  ⟨95,15915,15918,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15915) (rows 15918)⟩,
  ⟨106,15916,20056,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15916) (rows 20056)⟩,
  ⟨109,15916,15918,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15916) (rows 15918)⟩,
  ⟨128,15917,15918,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15917) (rows 15918)⟩,
  ⟨173,15918,15919,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15918) (rows 15919)⟩,
  ⟨192,15919,15920,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15919) (rows 15920)⟩,
])

checked_c898_fan route99 commonRaw99 :=
  ⟨1231,blockRows 40,46⟩ using c898_entries%(#[
  ⟨0,15928,20065,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15928) (rows 20065)⟩,
  ⟨46,15921,20065,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15921) (rows 20065)⟩,
  ⟨47,15923,20065,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15923) (rows 20065)⟩,
  ⟨95,15923,15926,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15923) (rows 15926)⟩,
  ⟨101,15924,20065,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15924) (rows 20065)⟩,
  ⟨110,15924,15926,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15924) (rows 15926)⟩,
  ⟨128,15925,15926,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15925) (rows 15926)⟩,
  ⟨174,15926,15927,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15926) (rows 15927)⟩,
  ⟨192,15927,15928,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15927) (rows 15928)⟩,
])

checked_c898_fan route100 commonRaw100 :=
  ⟨1232,blockRows 41,47⟩ using c898_entries%(#[
  ⟨0,15936,20074,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15936) (rows 20074)⟩,
  ⟨47,15929,20074,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15929) (rows 20074)⟩,
  ⟨48,15931,20074,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15931) (rows 20074)⟩,
  ⟨89,15931,15934,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15931) (rows 15934)⟩,
  ⟨95,15932,20074,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15932) (rows 20074)⟩,
  ⟨111,15932,15934,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15932) (rows 15934)⟩,
  ⟨128,15933,15934,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15933) (rows 15934)⟩,
  ⟨175,15934,15935,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15934) (rows 15935)⟩,
  ⟨192,15935,15936,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15935) (rows 15936)⟩,
])

checked_c898_fan route101 commonRaw101 :=
  ⟨1233,blockRows 42,48⟩ using c898_entries%(#[
  ⟨0,15944,20083,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15944) (rows 20083)⟩,
  ⟨48,15937,20083,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15937) (rows 20083)⟩,
  ⟨49,15940,20083,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15940) (rows 20083)⟩,
  ⟨112,15940,15942,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15940) (rows 15942)⟩,
  ⟨128,15941,15942,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15941) (rows 15942)⟩,
  ⟨177,15942,15943,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15942) (rows 15943)⟩,
  ⟨192,15943,15944,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15943) (rows 15944)⟩,
])

checked_c898_fan route102 commonRaw102 :=
  ⟨1234,blockRows 43,49⟩ using c898_entries%(#[
  ⟨0,15952,20093,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15952) (rows 20093)⟩,
  ⟨49,15945,20093,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15945) (rows 20093)⟩,
  ⟨50,15948,20093,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15948) (rows 20093)⟩,
  ⟨113,15948,15950,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15948) (rows 15950)⟩,
  ⟨128,15949,15950,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15949) (rows 15950)⟩,
  ⟨178,15950,15951,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15950) (rows 15951)⟩,
  ⟨192,15951,15952,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15951) (rows 15952)⟩,
])

checked_c898_fan route103 commonRaw103 :=
  ⟨1235,blockRows 44,50⟩ using c898_entries%(#[
  ⟨0,15960,20103,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15960) (rows 20103)⟩,
  ⟨50,15953,20103,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15953) (rows 20103)⟩,
  ⟨51,15956,20103,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15956) (rows 20103)⟩,
  ⟨115,15956,15958,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15956) (rows 15958)⟩,
  ⟨128,15957,15958,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15957) (rows 15958)⟩,
  ⟨178,15958,15959,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15958) (rows 15959)⟩,
  ⟨192,15959,15960,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15959) (rows 15960)⟩,
])

checked_c898_fan route104 commonRaw104 :=
  ⟨1236,blockRows 45,51⟩ using c898_entries%(#[
  ⟨0,15968,20113,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15968) (rows 20113)⟩,
  ⟨51,15961,20113,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15961) (rows 20113)⟩,
  ⟨52,15964,20113,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15964) (rows 20113)⟩,
  ⟨115,15964,15966,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15964) (rows 15966)⟩,
  ⟨128,15965,15966,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15965) (rows 15966)⟩,
  ⟨180,15966,15967,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15966) (rows 15967)⟩,
  ⟨192,15967,15968,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15967) (rows 15968)⟩,
])

checked_c898_fan route105 commonRaw105 :=
  ⟨1237,blockRows 46,52⟩ using c898_entries%(#[
  ⟨0,15976,20123,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15976) (rows 20123)⟩,
  ⟨52,15969,20123,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15969) (rows 20123)⟩,
  ⟨53,15972,20123,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15972) (rows 20123)⟩,
  ⟨117,15972,15974,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15972) (rows 15974)⟩,
  ⟨128,15973,15974,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15973) (rows 15974)⟩,
  ⟨181,15974,15975,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15974) (rows 15975)⟩,
  ⟨192,15975,15976,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15975) (rows 15976)⟩,
])

checked_c898_fan route106 commonRaw106 :=
  ⟨1238,blockRows 47,53⟩ using c898_entries%(#[
  ⟨0,15984,20133,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15984) (rows 20133)⟩,
  ⟨53,15977,20133,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15977) (rows 20133)⟩,
  ⟨54,15980,20133,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15980) (rows 20133)⟩,
  ⟨117,15980,15982,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15980) (rows 15982)⟩,
  ⟨128,15981,15982,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15981) (rows 15982)⟩,
  ⟨182,15982,15983,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15982) (rows 15983)⟩,
  ⟨192,15983,15984,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15983) (rows 15984)⟩,
])

checked_c898_fan route107 commonRaw107 :=
  ⟨1239,blockRows 48,54⟩ using c898_entries%(#[
  ⟨0,15992,20143,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15992) (rows 20143)⟩,
  ⟨54,15985,20143,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15985) (rows 20143)⟩,
  ⟨55,15988,20143,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15988) (rows 20143)⟩,
  ⟨119,15988,15990,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15988) (rows 15990)⟩,
  ⟨128,15989,15990,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15989) (rows 15990)⟩,
  ⟨182,15990,15991,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15990) (rows 15991)⟩,
  ⟨192,15991,15992,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15991) (rows 15992)⟩,
])

checked_c898_fan route108 commonRaw108 :=
  ⟨1240,blockRows 49,55⟩ using c898_entries%(#[
  ⟨0,16000,20153,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16000) (rows 20153)⟩,
  ⟨55,15993,20153,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15993) (rows 20153)⟩,
  ⟨56,15996,20153,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15996) (rows 20153)⟩,
  ⟨119,15996,15998,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15996) (rows 15998)⟩,
  ⟨128,15997,15998,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15997) (rows 15998)⟩,
  ⟨183,15998,15999,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15998) (rows 15999)⟩,
  ⟨192,15999,16000,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 15999) (rows 16000)⟩,
])

checked_c898_fan route109 commonRaw109 :=
  ⟨1249,blockRows 50,0⟩ using c898_entries%(#[
  ⟨0,16068,20226,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16068) (rows 20226)⟩,
  ⟨64,16064,20226,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16064) (rows 20226)⟩,
  ⟨65,16065,20226,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16065) (rows 20226)⟩,
  ⟨128,16065,16066,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16065) (rows 16066)⟩,
  ⟨192,16065,16067,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16065) (rows 16067)⟩,
  ⟨193,16064,16067,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16064) (rows 16067)⟩,
  ⟨208,16068,20226,materialize_basis% VertexSupport.Basis.fromRowsPrimitive (rows 16068) (rows 20226)⟩,
])

checked_c898_fan route110 commonRaw110 :=
  ⟨1628,[],0⟩ using c898_cycle%(cyclicDirections,[18794,18797,18798,16065,18800,18801])

checked_c898_fan route111 commonRaw111 :=
  ⟨1629,[],1⟩ using c898_cycle%(cyclicDirections,[18803,18806,18807,16072,18809])

checked_c898_fan route112 commonRaw112 :=
  ⟨1630,[],2⟩ using c898_cycle%(cyclicDirections,[18811,18813,18814,16077,18815,18816])

checked_c898_fan route113 commonRaw113 :=
  ⟨1631,[],3⟩ using c898_cycle%(cyclicDirections,[18818,18820,18821,16082,18822,18823])

checked_c898_fan route114 commonRaw114 :=
  ⟨1632,[],4⟩ using c898_cycle%(cyclicDirections,[18825,18827,18828,16087,18829,18830])

checked_c898_fan route115 commonRaw115 :=
  ⟨1633,[],5⟩ using c898_cycle%(cyclicDirections,[18832,18834,18835,16092,18836,18837])

checked_c898_fan route116 commonRaw116 :=
  ⟨1634,[],6⟩ using c898_cycle%(cyclicDirections,[18839,18841,18842,16097,18843,18844])

checked_c898_fan route117 commonRaw117 :=
  ⟨1635,[],7⟩ using c898_cycle%(cyclicDirections,[18846,18848,18849,16102,18850,18851])

checked_c898_fan route118 commonRaw118 :=
  ⟨1636,[],8⟩ using c898_cycle%(cyclicDirections,[18853,18855,18856,16107,18857,18858])

checked_c898_fan route119 commonRaw119 :=
  ⟨1637,[],9⟩ using c898_cycle%(cyclicDirections,[18866,18860,18861,18862,18863,16112,18864,18865])

checked_c898_fan route120 commonRaw120 :=
  ⟨1638,[],10⟩ using c898_cycle%(cyclicDirections,[18873,18867,18868,18869,18870,16117,18871,18872])

checked_c898_fan route121 commonRaw121 :=
  ⟨1639,[],11⟩ using c898_cycle%(cyclicDirections,[18880,18874,18875,18876,18877,16122,18878,18879])

checked_c898_fan route122 commonRaw122 :=
  ⟨1640,[],12⟩ using c898_cycle%(cyclicDirections,[18887,18881,18884,16127,18885,18886])

checked_c898_fan route123 commonRaw123 :=
  ⟨1641,[],13⟩ using c898_cycle%(cyclicDirections,[18893,18888,18890,16132,18891,18892])

checked_c898_fan route124 commonRaw124 :=
  ⟨1642,[],14⟩ using c898_cycle%(cyclicDirections,[18899,18894,18896,16137,18897,18898])

checked_c898_fan route125 commonRaw125 :=
  ⟨1643,[],15⟩ using c898_cycle%(cyclicDirections,[18905,18900,18902,16142,18903,18904])

checked_c898_fan route126 commonRaw126 :=
  ⟨1644,[],16⟩ using c898_cycle%(cyclicDirections,[18906,18908,16147,18909,18910])

checked_c898_fan route127 commonRaw127 :=
  ⟨1645,[],17⟩ using c898_cycle%(cyclicDirections,[18912,18914,16152,18915,18916])

end
end N12Compact.C898Cached.AllPairs
