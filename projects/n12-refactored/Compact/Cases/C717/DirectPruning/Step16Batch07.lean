import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step16Batch07 (N12Compact.C713Shared.dictionary) [
  plan845 (4739,(some [110488]),4746) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 5 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 4), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)]]
