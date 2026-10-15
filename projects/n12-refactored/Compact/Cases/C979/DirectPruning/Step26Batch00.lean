import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step26Batch00 (N12Compact.C713Shared.dictionary) [
  plan1471 (3986,(some [113780]),8621) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1472 (8736,(some [113781]),8622) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan1473 (8737,(some [113782]),8623) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 7], .direct (.copy 13)],
  plan1474 empty(8738),
  plan1475 empty(8739),
  plan1476 empty(8740),
  plan1477 empty(8741),
  plan1478 empty(8742),
  plan1479 empty(8743),
  plan1480 empty(8744),
  plan1481 empty(8745),
  plan1482 empty(8746),
  plan1483 empty(8747),
  plan1484 empty(8748),
  plan1485 empty(8749),
  plan1486 empty(8750)]
