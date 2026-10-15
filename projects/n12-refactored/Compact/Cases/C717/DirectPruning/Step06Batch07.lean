import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step06Batch07 (N12Compact.C713Shared.dictionary) [
  plan1598 empty(5387),
  plan1599 empty(5388),
  plan1600 empty(5389),
  plan1601 empty(5390),
  plan1602 empty(5391),
  plan1603 empty(5392),
  plan1604 empty(5393),
  plan1605 empty(5394),
  plan1606 empty(5395),
  plan1607 empty(5396),
  plan1608 empty(5397),
  plan1609 empty(5398),
  plan1610 empty(5399),
  plan1611 empty(5400),
  plan1612 (5401,(some [110966]),5468) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 7], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 8], .direct (.copy 13)],
  plan1613 (5402,(some [110967]),5469) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 8], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 4], .direct (.single 2), .block [.pair 0 8], .direct (.copy 13)]]
