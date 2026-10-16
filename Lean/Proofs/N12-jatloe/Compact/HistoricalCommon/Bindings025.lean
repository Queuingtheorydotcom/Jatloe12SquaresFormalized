import Compact.Bridge.CheckedCommonContext
import Compact.Bridge.CheckedCommonFanCommand
import Compact.Cases.C713.SharedDictionary
import Compact.HistoricalCommon.Bindings024
import Compact.HistoricalData.SharedFanBlocks
import Compact.HistoricalFans.C701_713_717_973_978_979.Directions

namespace N12Compact.HistoricalCommon
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false
noncomputable section

bind_common_context context800 (dictionary,context799_cache) := ⟨100,fanBlockRows 59⟩
checked_common_fan context801 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨101,[]⟩ using [697,691,692,693,694,695,696]
bind_common_context context802 (dictionary,context801_cache) := ⟨101,fanBlockRows 59⟩
checked_common_fan context803 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨102,[]⟩ using [704,698,699,700,701,702,703]
bind_common_context context804 (dictionary,context803_cache) := ⟨102,fanBlockRows 59⟩
checked_common_fan context805 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨103,[]⟩ using [711,705,706,707,708,709,710]
bind_common_context context806 (dictionary,context805_cache) := ⟨103,fanBlockRows 59⟩
checked_common_fan context807 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨67,fanBlockRows 334⟩ using [108990,84540,84541,84542,84543,84544,84545,471,472,473,474]
checked_common_fan context808 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨104,[]⟩ using [717,712,713,714,715,716]
bind_common_context context809 (dictionary,context808_cache) := ⟨104,fanBlockRows 59⟩
checked_common_fan context810 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨105,[]⟩ using [724,718,719,720,721,722,723]
bind_common_context context811 (dictionary,context810_cache) := ⟨105,fanBlockRows 59⟩
checked_common_fan context812 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨106,[]⟩ using [731,725,726,727,728,729,730]
bind_common_context context813 (dictionary,context812_cache) := ⟨106,fanBlockRows 59⟩
checked_common_fan context814 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨107,[]⟩ using [739,732,733,734,735,736,737,738]
bind_common_context context815 (dictionary,context814_cache) := ⟨107,fanBlockRows 59⟩
checked_common_fan context816 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨108,fanBlockRows 335⟩ using [747,740,108991,742,743,744,745,746]
checked_common_fan context817 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨109,fanBlockRows 336⟩ using [755,748,108992,750,751,752,753,754]
checked_common_fan context818 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨110,fanBlockRows 337⟩ using [763,756,108993,760,761,762]
checked_common_fan context819 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨111,fanBlockRows 338⟩ using [771,764,108994,768,769,770]
checked_common_fan context820 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨112,fanBlockRows 339⟩ using [779,772,108995,776,777,778]
checked_common_fan context821 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨113,fanBlockRows 340⟩ using [787,780,108996,784,785,786]
checked_common_fan context822 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨68,fanBlockRows 341⟩ using [108997,84559,84560,84561,479,480,481,482]
checked_common_fan context823 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨114,fanBlockRows 342⟩ using [795,788,108998,792,793,794]
checked_common_fan context824 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨115,fanBlockRows 343⟩ using [803,796,108999,800,801,802]
checked_common_fan context825 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨116,fanBlockRows 344⟩ using [811,804,109000,808,809,810]
checked_common_fan context826 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨117,fanBlockRows 345⟩ using [818,812,109001,815,816,817]
checked_common_fan context827 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨118,fanBlockRows 346⟩ using [825,819,109002,822,823,824]
checked_common_fan context828 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨119,fanBlockRows 347⟩ using [833,826,109003,829,830,831,832]
checked_common_fan context829 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨120,fanBlockRows 348⟩ using [841,834,109004,837,838,839,840]
checked_common_fan context830 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨121,fanBlockRows 349⟩ using [849,842,109005,845,846,847,848]
checked_common_fan context831 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨122,fanBlockRows 350⟩ using [857,850,109006,84574,84575,855,856]

end
end N12Compact.HistoricalCommon
