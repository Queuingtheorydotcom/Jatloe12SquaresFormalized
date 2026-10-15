import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step21Batch01 (N12Compact.C713Shared.dictionary) [
  plan655 (6803,(some [111815]),6866) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan656 (6804,(some [111816]),6867) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan657 empty(6805),
  plan658 empty(6806),
  plan659 (6807,(some [111818]),6868) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 4), .direct (.single 2), .block [.pair 0 6], .direct (.copy 13)],
  plan660 empty(6808),
  plan661 empty(6809),
  plan662 empty(6810),
  plan663 empty(6811),
  plan664 empty(6812),
  plan665 empty(6813),
  plan666 empty(6814),
  plan667 empty(6815),
  plan668 empty(6816),
  plan669 empty(6817),
  plan670 empty(6818)]
