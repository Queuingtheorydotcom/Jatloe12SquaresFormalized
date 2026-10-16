import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings216
import Compact.HistoricalCommon.Bindings256
import Compact.HistoricalCommon.Bindings257
import Compact.HistoricalCommon.Bindings258
import Compact.HistoricalCommon.Bindings259
import Compact.HistoricalCommon.Bindings260
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C973.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 64 → Context dictionary :=
  ![context8199,context8273,context8284,context8295,context8306,context8317,context8322,context8323,context8324,context8325,context8263,context8264,context8265,context8266,context8267,context8268,context8269,context8270,context8271,context8272,context8274,context8275,context8276,context8277,context8278,context8279,context8280,context8281,context8282,context8283,context8285,context8286,context8287,context8288,context8289,context8290,context8291,context8292,context8293,context8294,context8296,context8297,context8298,context8299,context8300,context8301,context8302,context8303,context8304,context8305,context8307,context8308,context8309,context8310,context8311,context8312,context8313,context8314,context8315,context8316,context8318,context8319,context8320,context8321]

def neighbors : Fin 64 → Context dictionary :=
  ![context8200,context8201,context8202,context8203,context8204,context8205,context8206,context8207,context8208,context8209,context8210,context8211,context8212,context8213,context8214,context8215,context8216,context8217,context8218,context8219,context8220,context8221,context8222,context8223,context8224,context8225,context8226,context8227,context8228,context6923,context8229,context8230,context8231,context8232,context8233,context8234,context8235,context8236,context8237,context8238,context8239,context8240,context8241,context8242,context8243,context8244,context8245,context8246,context8247,context8248,context8249,context8250,context8251,context8252,context8253,context8254,context8255,context8256,context8257,context8258,context8259,context8260,context8261,context8262]


end
end N12Compact.HistoricalCommon.C973.Step04
