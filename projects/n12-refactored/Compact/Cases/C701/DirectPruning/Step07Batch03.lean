import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step07Batch03 (N12Compact.C713Shared.dictionary) [
  plan1263 (1521,none,1573) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1264 (1522,none,1574) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1265 (1523,none,1575) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1266 (1524,none,1576) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)]]
