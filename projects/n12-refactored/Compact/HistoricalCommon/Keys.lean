import Compact.Cases.C713.SharedDictionary

namespace N12Compact.HistoricalCommon
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def angleRank : Array Nat := #[1,4,7,10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82,85,88,91,94,97,100,103,106,109,112,115,118,121,124,127,130,133,136,139,142,145,148,151,154,157,160,163,166,169,172,175,178,181,184,187,190,0,2,3,5,6,8,9,11,12,14,15,17,18,20,21,23,24,26,27,29,30,32,33,35,36,38,39,41,42,44,45,47,48,50,51,53,54,56,57,59,60,62,63,65,66,68,69,71,72,74,75,77,78,80,81,83,84,86,87,89,90,92,93,95,96,98,99,101,102,104,105,107,108,110,111,113,114,116,117,119,120,122,123,125,126,128,129,131,132,134,135,137,138,140,141,143,144,146,147,149,150,152,153,155,156,158,159,161,162,164,165,167,168,170,171,173,174,176,177,179,180,182,183,185,186,188,189,191]

def ownKeys (angle : Nat) (i : Fin 4) : Nat :=
  (angleRank[angle]?).getD 0 + 192 * (![0,2,1,3] i)

def pairKeys (source neighbor : Nat) (i : Fin 8) : Nat :=
  if h : i.val < 4 then ownKeys source ⟨i.val,h⟩
  else ownKeys neighbor ⟨i.val-4,by omega⟩

def opposite (key : Nat) : Nat := (key+384)%768

end
end N12Compact.HistoricalCommon
