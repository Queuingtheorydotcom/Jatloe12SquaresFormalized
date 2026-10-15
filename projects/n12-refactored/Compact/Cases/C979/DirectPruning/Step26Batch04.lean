import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step26Batch04 (N12Compact.C713Shared.dictionary) [
  plan1535 empty(8799),
  plan1536 empty(8800),
  plan1537 (4098,(some [113783]),8624) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 6], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .direct (.single 0), .block [.pair 0 6], .direct (.copy 12)]]
