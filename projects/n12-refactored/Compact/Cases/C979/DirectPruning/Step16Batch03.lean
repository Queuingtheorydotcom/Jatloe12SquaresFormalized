import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step16Batch03 (N12Compact.C713Shared.dictionary) [
  plan838 empty(3794),
  plan839 empty(3795),
  plan840 empty(3796),
  plan841 empty(3797),
  plan842 empty(3798),
  plan843 empty(3799),
  plan844 empty(3800),
  plan845 empty(3801),
  plan846 empty(3802),
  plan847 empty(3803),
  plan848 empty(3804),
  plan849 empty(3805),
  plan850 empty(3806),
  plan851 (3807,(some [113420]),11992) [.direct (.pair 0 1), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 2], .direct (.single 1), .block [.pair 0 1], .direct (.copy 12)],
  plan852 (3808,(some [113421]),11993) [.direct (.pair 0 1), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 1), .block [.pair 0 1], .direct (.copy 12)],
  plan853 (3809,(some [113422]),11994) [.direct (.pair 0 1), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 1), .block [.pair 0 1], .direct (.copy 12)]]
