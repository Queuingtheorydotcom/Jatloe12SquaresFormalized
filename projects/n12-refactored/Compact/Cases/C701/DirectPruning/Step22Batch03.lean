import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step22Batch03 (N12Compact.C713Shared.dictionary) [
  plan683 empty(1086),
  plan684 empty(1087),
  plan685 empty(1088),
  plan686 empty(1089),
  plan687 empty(1090),
  plan688 empty(1091),
  plan689 empty(1092),
  plan690 empty(1093),
  plan691 empty(1094),
  plan692 empty(1095),
  plan693 empty(1096),
  plan694 (1097,(some [109061]),1120) [.block [.pair 0 1], .block [.pair 0 3], .direct (.single 2), .direct (.pair 2 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 12)],
  plan695 (1098,(some [109063]),1121) [.block [.pair 0 1], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 2 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 2), .block [.pair 0 3], .direct (.single 4), .direct (.copy 12)],
  plan696 (1099,(some [109064]),1122) [.block [.pair 0 4], .direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 2 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 12)],
  plan697 (1100,(some [109065]),1123) [.block [.pair 0 1], .direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 2 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 12)],
  plan698 (1101,(some [109066]),1124) [.block [.pair 0 1], .direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 2 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 12)]]
