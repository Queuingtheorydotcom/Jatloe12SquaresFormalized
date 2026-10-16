import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step18Batch02 (N12Compact.C713Shared.dictionary) [
  plan454 empty(96),
  plan455 empty(97),
  plan456 empty(98),
  plan457 empty(99),
  plan458 empty(100),
  plan459 empty(101),
  plan460 empty(102),
  plan461 empty(103),
  plan462 empty(104),
  plan463 empty(105),
  plan464 empty(106),
  plan465 empty(107),
  plan466 (108,(some [108991]),148) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 12)],
  plan467 (109,(some [108992]),149) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 12)],
  plan468 (110,(some [108993]),150) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 0), .block [.pair 0 5], .direct (.copy 12)],
  plan469 (111,(some [108994]),151) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 0), .block [.pair 0 5], .direct (.copy 12)]]
