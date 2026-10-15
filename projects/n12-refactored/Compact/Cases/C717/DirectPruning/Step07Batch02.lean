import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step07Batch02 (N12Compact.C713Shared.dictionary) [
  plan1646 (5435,(some [111029]),5491) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1647 (5436,(some [111030]),5492) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan1648 (5437,(some [111031]),5493) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan1649 (5438,(some [111032]),5494) [.block [.pair 0 7], .block [.pair 0 5], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .block [.pair 0 5], .block [.pair 0 7], .direct (.single 5), .direct (.copy 12)],
  plan1650 empty(5439),
  plan1651 empty(5440),
  plan1652 empty(5441),
  plan1653 empty(5442),
  plan1654 empty(5443),
  plan1655 empty(5444),
  plan1656 empty(5445),
  plan1657 empty(5446),
  plan1658 empty(5447),
  plan1659 empty(5448),
  plan1660 empty(5449),
  plan1661 empty(5450)]
