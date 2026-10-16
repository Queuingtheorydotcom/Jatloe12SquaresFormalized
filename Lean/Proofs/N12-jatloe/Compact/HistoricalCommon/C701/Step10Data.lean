import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings005
import Compact.HistoricalCommon.Bindings006
import Compact.HistoricalCommon.Bindings007
import Compact.HistoricalCommon.Bindings008
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step10
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 59 → Context dictionary :=
  ![context255,context266,context270,context271,context272,context273,context170,context216,context217,context218,context219,context220,context221,context222,context223,context224,context225,context226,context227,context228,context229,context230,context231,context232,context233,context234,context235,context236,context237,context238,context239,context240,context241,context242,context243,context244,context245,context246,context247,context248,context249,context250,context251,context252,context253,context254,context256,context257,context258,context259,context260,context261,context262,context263,context264,context265,context267,context268,context269]

def neighbors : Fin 45 → Context dictionary :=
  ![context171,context172,context173,context174,context175,context176,context177,context178,context179,context180,context181,context182,context183,context184,context185,context186,context187,context188,context189,context190,context191,context192,context193,context194,context195,context196,context197,context198,context199,context200,context201,context202,context203,context204,context205,context206,context207,context208,context209,context210,context211,context212,context213,context214,context215]


end
end N12Compact.HistoricalCommon.C701.Step10
