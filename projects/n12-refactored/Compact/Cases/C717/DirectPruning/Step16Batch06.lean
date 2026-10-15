import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step16Batch06 (N12Compact.C713Shared.dictionary) [
  plan829 empty(4723),
  plan830 empty(4724),
  plan831 empty(4725),
  plan832 empty(4726),
  plan833 empty(4727),
  plan834 empty(4728),
  plan835 empty(4729),
  plan836 empty(4730),
  plan837 empty(4731),
  plan838 empty(4732),
  plan839 empty(4733),
  plan840 (4734,(some [110483]),4741) [.block [.pair 0 5], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.pair 4 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 3), .block [.pair 0 3], .direct (.single 4), .direct (.copy 11)],
  plan841 (4735,(some [110484]),4742) [.block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.pair 5 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 4), .block [.pair 0 4], .direct (.single 5), .direct (.copy 12)],
  plan842 (4736,(some [110485]),4743) [.block [.pair 0 6], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.pair 4 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 4), .block [.pair 0 4], .direct (.single 5), .direct (.copy 12)],
  plan843 (4737,(some [110486]),4744) [.block [.pair 0 6], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.pair 5 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 4), .block [.pair 0 4], .direct (.single 5), .direct (.copy 12)],
  plan844 (4738,(some [110487]),4745) [.block [.pair 0 2], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.pair 4 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 4), .block [.pair 0 4], .direct (.single 5), .direct (.copy 12)]]
