import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step07Batch01 (N12Compact.C713Shared.dictionary) [
  plan1630 (5419,(some [111024]),5486) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1631 (5420,(some [111025]),5487) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1632 empty(5421),
  plan1633 empty(5422),
  plan1634 empty(5423),
  plan1635 empty(5424),
  plan1636 empty(5425),
  plan1637 empty(5426),
  plan1638 empty(5427),
  plan1639 empty(5428),
  plan1640 empty(5429),
  plan1641 empty(5430),
  plan1642 empty(5431),
  plan1643 (5432,(some [111026]),5488) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1644 (5433,(some [111027]),5489) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1645 (5434,(some [111028]),5490) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)]]
