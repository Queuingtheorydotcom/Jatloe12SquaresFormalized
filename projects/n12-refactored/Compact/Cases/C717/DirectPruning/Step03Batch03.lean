import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step03Batch03 (N12Compact.C713Shared.dictionary) [
  plan1150 (4547,none,4795) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1151 (4548,none,4796) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1152 (4549,none,4797) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1153 (4550,none,4798) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1154 (4551,none,4799) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1155 (4552,none,4800) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1156 (4553,none,4801) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1157 (4554,none,4802) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1158 (4555,none,4803) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1159 (4556,none,4804) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1160 (4557,none,4805) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1161 (4558,none,4806) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1162 (4559,none,4807) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1163 (4560,none,4808) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1164 (4561,none,4809) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 3), .direct (.single 1), .direct (.single 4), .direct (.copy 10)],
  plan1165 (4562,(some [110702]),4810) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 4), .direct (.copy 10)]]
