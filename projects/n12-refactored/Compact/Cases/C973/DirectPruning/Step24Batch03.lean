import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step24Batch03 (N12Compact.C713Shared.dictionary) [
  plan878 (7580,(some [111960]),7695) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan879 (7581,(some [111961]),7696) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan880 (7582,(some [111963]),7697) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan881 (7583,(some [111964]),7698) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 8], .direct (.copy 13)],
  plan882 (7584,(some [97156,97155,97154,111965]),7699) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5, .pair 0 7, .pair 0 7, .pair 0 7], .direct (.pair 6 7), .direct (.single 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .direct (.single 3), .direct (.single 1), .direct (.single 7), .direct (.copy 14)],
  plan883 (7585,(some [97163,97162,97161,111966]),7700) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5, .pair 0 6, .pair 0 6, .pair 0 6], .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)]]
