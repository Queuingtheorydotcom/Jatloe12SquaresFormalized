import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C713DirectPruning.Step03Batch02 (N12Compact.C713Shared.dictionary) [
  plan408 (2777,(some [109695]),2905) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan409 (2778,(some [109696]),2906) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan410 (2779,(some [109697]),2907) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan411 (2780,(some [109698]),2908) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan412 empty(2781),
  plan413 empty(2782),
  plan414 empty(2783),
  plan415 empty(2784),
  plan416 empty(2785),
  plan417 empty(2786),
  plan418 empty(2787),
  plan419 empty(2788),
  plan420 empty(2789),
  plan421 empty(2790),
  plan422 empty(2791),
  plan423 empty(2792)]
