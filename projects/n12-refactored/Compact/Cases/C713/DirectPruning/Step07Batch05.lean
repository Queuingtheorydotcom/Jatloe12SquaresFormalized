import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C713DirectPruning.Step07Batch05 (N12Compact.C713Shared.dictionary) [
  plan798 (3478,(some [109922]),3527) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 11)],
  plan799 (3479,(some [109923]),3528) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 11)],
  plan800 empty(3480),
  plan801 empty(3481),
  plan802 empty(3482),
  plan803 empty(3483),
  plan804 empty(3484),
  plan805 empty(3485),
  plan806 empty(3486),
  plan807 empty(3487),
  plan808 empty(3488),
  plan809 empty(3489),
  plan810 empty(3490),
  plan811 empty(3491),
  plan812 empty(3492),
  plan813 empty(3493)]
