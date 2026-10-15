import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C713DirectPruning.Step02Batch01 (N12Compact.C713Shared.dictionary) [
  plan272 (2566,(some [86057,86056,86055,86054,109601]),2686) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 4, .pair 0 7, .pair 0 7, .pair 0 7, .pair 0 7], .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .block [.pair 0 4, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .direct (.copy 11)],
  plan273 (2567,(some [86066,86065,86064,86063,109602]),2687) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2, .pair 0 6, .pair 0 7, .pair 0 7], .direct (.single 6), .direct (.single 6), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .direct (.single 0), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .direct (.copy 11)],
  plan274 (2568,(some [86074,86073,86072,109603]),2688) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2, .pair 0 6, .pair 0 7], .direct (.single 6), .direct (.single 6), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .direct (.single 0), .block [.pair 0 2, .pair 0 2, .pair 0 2, .pair 0 2], .direct (.copy 11)],
  plan275 (2569,(some [86079,109604]),2689) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 7], .direct (.single 6), .direct (.single 6), .block [.pair 0 2, .pair 0 2], .direct (.single 0), .block [.pair 0 2, .pair 0 2], .direct (.copy 11)],
  plan276 (2570,(some [109605]),2690) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 1], .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 2], .direct (.copy 11)],
  plan277 (2571,(some [109606]),2691) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 1], .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 2], .direct (.copy 11)],
  plan278 empty(2572),
  plan279 empty(2573),
  plan280 empty(2574),
  plan281 empty(2575),
  plan282 empty(2576),
  plan283 empty(2577),
  plan284 empty(2578),
  plan285 empty(2579),
  plan286 empty(2580),
  plan287 empty(2581)]
