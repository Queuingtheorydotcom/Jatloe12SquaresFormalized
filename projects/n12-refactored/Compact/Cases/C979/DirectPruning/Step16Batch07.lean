import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step16Batch07 (N12Compact.C713Shared.dictionary) [
  plan902 (11968,(some [103978,103977,103976,103975,103974,103973,103972,113402]),12034) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3], .block [.pair 0 3, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 7], .block [.pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3], .direct (.single 0), .block [.pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7], .direct (.copy 12)],
  plan903 (11969,(some [103987,113403]),12035) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 3], .block [.pair 0 3, .pair 0 7], .block [.pair 0 7, .pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3, .pair 0 3], .direct (.single 0), .block [.pair 0 7, .pair 0 7], .direct (.copy 12)]]
