import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step16Batch03 (N12Compact.C713Shared.dictionary) [
  plan353 (1882,(some [84404,108914]),1934) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .block [.pair 0 5, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan354 (1883,(some [84407,108915]),1935) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .block [.pair 0 5, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan355 (1884,(some [84411,108917]),1936) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .block [.pair 0 5, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan356 (1885,(some [84414,108918]),1937) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .block [.pair 0 5, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan357 (1886,(some [84418,84417,108919]),1938) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .block [.pair 0 5, .pair 0 5, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .direct (.single 0), .direct (.single 4), .direct (.copy 11)]]
