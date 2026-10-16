import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step08Batch02 (N12Compact.C713Shared.dictionary) [
  plan2404 (8656,(some [85405]),8767) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan2405 (8657,(some [85408]),8768) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan2406 empty(8658),
  plan2407 empty(8659),
  plan2408 empty(8660),
  plan2409 empty(8661),
  plan2410 empty(8662),
  plan2411 empty(8663),
  plan2412 empty(8664),
  plan2413 empty(8665),
  plan2414 empty(8666),
  plan2415 empty(8667),
  plan2416 empty(8668),
  plan2417 empty(8669),
  plan2418 empty(8670),
  plan2419 empty(8671)]
