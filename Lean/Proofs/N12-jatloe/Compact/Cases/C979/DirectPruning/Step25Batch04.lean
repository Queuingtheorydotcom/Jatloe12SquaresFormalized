import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step25Batch04 (N12Compact.C713Shared.dictionary) [
  plan1469 (12034,(some [113778]),12076) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan1470 (12035,(some [113779]),12077) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)]]
