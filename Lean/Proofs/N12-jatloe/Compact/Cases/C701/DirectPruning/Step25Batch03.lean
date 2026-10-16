import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step25Batch03 (N12Compact.C713Shared.dictionary) [
  plan806 (426,none,478) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan807 (427,none,479) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 4), .direct (.single 2), .direct (.single 6), .direct (.copy 13)],
  plan808 (428,none,480) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan809 (429,none,481) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)]]
