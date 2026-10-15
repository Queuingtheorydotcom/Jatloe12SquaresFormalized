import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step11Batch07 (N12Compact.C713Shared.dictionary) [
  plan258 (3858,none,5887) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 0), .direct (.single 6), .direct (.copy 13)],
  plan259 (3859,none,5888) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 0), .direct (.single 6), .direct (.copy 13)]]
