import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C978DirectPruning.Step14Batch00 (N12Compact.C713Shared.dictionary) [
  plan192 (8053,none,8096) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 1), .direct (.single 0), .direct (.single 3), .direct (.copy 10)],
  plan193 (8054,(some [112716]),8097) [.block [.pair 0 1], .direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 1), .direct (.single 0), .direct (.single 3), .direct (.copy 10)],
  plan194 (8055,(some [112717]),8098) [.block [.pair 0 1], .direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 1), .direct (.single 0), .direct (.single 3), .direct (.copy 10)],
  plan195 empty(8056),
  plan196 empty(8057),
  plan197 empty(8058),
  plan198 empty(8059),
  plan199 empty(8060),
  plan200 empty(8061),
  plan201 empty(8062),
  plan202 empty(8063),
  plan203 empty(8064),
  plan204 empty(8065),
  plan205 empty(8066),
  plan206 empty(8067),
  plan207 empty(8068)]
