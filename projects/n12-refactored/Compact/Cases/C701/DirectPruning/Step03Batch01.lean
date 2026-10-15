import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step03Batch01 (N12Compact.C713Shared.dictionary) [
  plan1058 (756,(some [108508]),820) [.block [.pair 0 1], .block [.pair 0 2], .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .direct (.single 1), .block [.pair 0 2], .direct (.single 2), .direct (.copy 10)],
  plan1059 (757,(some [108510]),821) [.block [.pair 0 1], .block [.pair 0 2], .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .direct (.single 1), .block [.pair 0 2], .direct (.single 2), .direct (.copy 10)],
  plan1060 (758,(some [108512]),822) [.block [.pair 0 1], .block [.pair 0 2], .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .direct (.single 1), .block [.pair 0 2], .direct (.single 2), .direct (.copy 10)],
  plan1061 (759,(some [108514]),823) [.block [.pair 0 1], .block [.pair 0 2], .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .direct (.single 1), .block [.pair 0 2], .direct (.single 2), .direct (.copy 10)],
  plan1062 empty(760),
  plan1063 empty(761),
  plan1064 empty(762),
  plan1065 empty(763),
  plan1066 empty(764),
  plan1067 empty(765),
  plan1068 empty(766),
  plan1069 empty(767),
  plan1070 empty(768),
  plan1071 empty(769),
  plan1072 empty(770),
  plan1073 empty(771)]
