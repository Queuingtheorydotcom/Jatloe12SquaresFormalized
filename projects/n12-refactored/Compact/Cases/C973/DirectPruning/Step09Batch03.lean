import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step09Batch03 (N12Compact.C713Shared.dictionary) [
  plan1397 (7749,(some [112321]),7526) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1398 (7750,(some [112322]),7527) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1399 (7751,(some [112324]),7528) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1400 (7752,(some [112325]),7529) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan1401 (7753,none,7530) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .direct (.single 3), .direct (.single 1), .direct (.single 7), .direct (.copy 14)],
  plan1402 (7754,none,7531) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .direct (.single 3), .direct (.single 1), .direct (.single 6), .direct (.copy 14)]]
