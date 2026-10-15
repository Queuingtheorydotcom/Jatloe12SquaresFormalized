import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step08Batch03 (N12Compact.C713Shared.dictionary) [
  plan1315 (1573,(some [109298]),1618) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan1316 (1574,(some [109299]),1619) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan1317 (1575,(some [85178,109301]),1620) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5, .pair 0 5], .block [.pair 0 5, .pair 0 1], .block [.pair 0 1, .pair 0 1], .block [.pair 0 1, .pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5, .pair 0 5], .direct (.copy 12)],
  plan1318 (1576,none,1621) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)]]
