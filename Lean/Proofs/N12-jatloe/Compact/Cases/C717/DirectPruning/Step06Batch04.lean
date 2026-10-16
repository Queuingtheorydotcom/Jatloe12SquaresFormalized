import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step06Batch04 (N12Compact.C713Shared.dictionary) [
  plan1550 empty(5339),
  plan1551 empty(5340),
  plan1552 empty(5341),
  plan1553 empty(5342),
  plan1554 empty(5343),
  plan1555 empty(5344),
  plan1556 empty(5345),
  plan1557 empty(5346),
  plan1558 empty(5347),
  plan1559 empty(5348),
  plan1560 empty(5349),
  plan1561 empty(5350),
  plan1562 (5351,(some [110992]),5432) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 9], .direct (.pair 0 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 9], .direct (.copy 14)],
  plan1563 (5352,(some [110993]),5433) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.pair 0 9), .direct (.single 10), .direct (.single 10), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.copy 15)],
  plan1564 (5353,(some [110994]),5434) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.pair 0 9), .direct (.single 10), .direct (.single 10), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.copy 15)],
  plan1565 (5354,(some [110995]),5435) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.pair 0 9), .direct (.single 10), .direct (.single 10), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 10], .direct (.copy 15)]]
