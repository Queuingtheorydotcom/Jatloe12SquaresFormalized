import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C978DirectPruning.Step02Batch00 (N12Compact.C713Shared.dictionary) [
  plan302 (8527,(some [101284,112718]),8591) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 2], .block [.pair 0 3, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3, .pair 0 2], .direct (.single 1), .direct (.single 6), .direct (.copy 14)],
  plan303 (8528,(some [101287,112719]),8592) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 2], .block [.pair 0 3, .pair 0 8], .block [.pair 0 8, .pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3, .pair 0 2], .direct (.single 1), .block [.pair 0 8, .pair 0 8], .direct (.copy 14)],
  plan304 (8529,(some [112720]),8593) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3], .direct (.single 1), .direct (.single 6), .direct (.copy 14)],
  plan305 (8530,(some [112721]),8594) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 8], .direct (.copy 14)],
  plan306 (8531,(some [112722]),8595) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 9], .direct (.pair 0 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 9], .direct (.copy 14)],
  plan307 (8532,(some [112723]),8596) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 9], .direct (.pair 0 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 9], .direct (.copy 14)],
  plan308 (8533,(some [112726]),8597) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 8], .direct (.copy 13)],
  plan309 (8534,(some [112727]),8598) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 5], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 8], .direct (.copy 13)],
  plan310 (8535,(some [112728]),8599) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 8], .direct (.copy 13)],
  plan311 (8536,(some [112729]),8600) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan312 empty(8537),
  plan313 empty(8538),
  plan314 empty(8539),
  plan315 empty(8540),
  plan316 empty(8541),
  plan317 empty(8542)]
