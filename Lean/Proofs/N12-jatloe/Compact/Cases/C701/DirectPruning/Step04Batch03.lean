import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step04Batch03 (N12Compact.C713Shared.dictionary) [
  plan1154 (852,(some [84962,109188]),877) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2, .pair 0 5], .block [.pair 0 2, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 1), .direct (.single 0), .block [.pair 0 2, .pair 0 5], .direct (.copy 11)],
  plan1155 (853,(some [84965,109189]),878) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2, .pair 0 5], .block [.pair 0 2, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 1), .direct (.single 0), .block [.pair 0 2, .pair 0 5], .direct (.copy 11)]]
