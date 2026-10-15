import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step15Batch00 (N12Compact.C713Shared.dictionary) [
  plan699 (11714,(some [113359]),11805) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 4], .direct (.copy 12)],
  plan700 (11715,(some [113360]),11806) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan701 (11716,(some [113361]),11807) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 4), .direct (.single 1), .block [.pair 0 6], .direct (.copy 13)],
  plan702 (11717,(some [113362]),11808) [.block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 3], .block [.pair 0 3], .direct (.single 4), .block [.pair 0 3], .block [.pair 0 5], .direct (.copy 13)],
  plan703 empty(11718),
  plan704 empty(11719),
  plan705 empty(11720),
  plan706 empty(11721),
  plan707 empty(11722),
  plan708 empty(11723),
  plan709 empty(11724),
  plan710 empty(11725),
  plan711 empty(11726),
  plan712 empty(11727),
  plan713 empty(11728),
  plan714 empty(11729)]
