import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step04Batch00 (N12Compact.C713Shared.dictionary) [
  plan1106 (804,(some [109170]),854) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 1), .direct (.single 0), .block [.pair 0 2], .direct (.copy 11)],
  plan1107 (805,(some [109171]),855) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .direct (.single 1), .direct (.single 0), .block [.pair 0 2], .direct (.copy 10)],
  plan1108 (806,(some [109172]),856) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 1], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .direct (.single 1), .direct (.single 0), .block [.pair 0 2], .direct (.copy 10)],
  plan1109 (807,(some [109179]),857) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1110 (808,(some [109190]),858) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1111 (809,(some [109191]),859) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1112 (810,(some [109192]),860) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1113 (811,(some [109193]),861) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1114 (812,(some [109194]),862) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 3], .direct (.copy 10)],
  plan1115 empty(813),
  plan1116 empty(814),
  plan1117 empty(815),
  plan1118 empty(816),
  plan1119 empty(817),
  plan1120 empty(818),
  plan1121 empty(819)]
