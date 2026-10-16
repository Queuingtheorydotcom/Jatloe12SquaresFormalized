import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings128
import Compact.HistoricalCommon.Bindings129
import Compact.HistoricalCommon.Bindings130
import Compact.HistoricalCommon.Bindings131
import Compact.HistoricalCommon.Bindings132
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C717.Step12
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 104 → Context dictionary :=
  ![context4097,context4139,context4150,context4161,context4172,context4183,context4194,context4205,context4216,context4227,context4129,context4130,context4131,context4132,context4133,context4134,context4135,context4136,context4137,context4138,context4140,context4141,context4142,context4143,context4144,context4145,context4146,context4147,context4148,context4149,context4151,context4152,context4153,context4154,context4155,context4156,context4157,context4158,context4159,context4160,context4162,context4163,context4164,context4165,context4166,context4167,context4168,context4169,context4170,context4171,context4173,context4174,context4175,context4176,context4177,context4178,context4179,context4180,context4181,context4182,context4184,context4185,context4186,context4187,context4188,context4189,context4190,context4191,context4192,context4193,context4195,context4196,context4197,context4198,context4199,context4200,context4201,context4202,context4203,context4204,context4206,context4207,context4208,context4209,context4210,context4211,context4212,context4213,context4214,context4215,context4217,context4218,context4219,context4220,context4221,context4222,context4223,context4224,context4225,context4226,context4125,context4126,context4127,context4128]

def neighbors : Fin 27 → Context dictionary :=
  ![context4098,context4099,context4100,context4101,context4102,context4103,context4104,context4105,context4106,context4107,context4108,context4109,context4110,context4111,context4112,context4113,context4114,context4115,context4116,context4117,context4118,context4119,context4120,context4121,context4122,context4123,context4124]


end
end N12Compact.HistoricalCommon.C717.Step12
