import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step21Batch02 (N12Compact.C713Shared.dictionary) [
  plan622 empty(673),
  plan623 empty(674),
  plan624 empty(675),
  plan625 empty(676),
  plan626 empty(677),
  plan627 empty(678),
  plan628 empty(679),
  plan629 empty(680),
  plan630 empty(681),
  plan631 empty(682),
  plan632 (683,(some [84704,109043]),692) [.direct (.single 0), .block [.pair 0 5, .pair 0 1], .block [.pair 0 5, .pair 0 1], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5, .pair 0 1], .direct (.single 0), .direct (.single 5), .direct (.copy 11)],
  plan633 (684,(some [84707,109044]),693) [.direct (.single 0), .block [.pair 0 4, .pair 0 1], .block [.pair 0 4, .pair 0 1], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4, .pair 0 1], .direct (.single 0), .direct (.single 4), .direct (.copy 10)],
  plan634 (685,(some [84710,109045]),694) [.direct (.single 0), .block [.pair 0 5, .pair 0 1], .block [.pair 0 5, .pair 0 1], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5, .pair 0 1], .direct (.single 0), .direct (.single 5), .direct (.copy 11)]]
