import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step16Batch01 (N12Compact.C713Shared.dictionary) [
  plan806 (3762,(some [113409]),11986) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan807 (3763,(some [113410]),11987) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan808 (3764,(some [113411]),11988) [.direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan809 (3765,(some [113412]),11989) [.direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan810 (3766,(some [113414]),11990) [.direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan811 (3767,(some [113415]),11991) [.direct (.single 1), .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan812 empty(3768),
  plan813 empty(3769),
  plan814 empty(3770),
  plan815 empty(3771),
  plan816 empty(3772),
  plan817 empty(3773),
  plan818 empty(3774),
  plan819 empty(3775),
  plan820 empty(3776),
  plan821 empty(3777)]
