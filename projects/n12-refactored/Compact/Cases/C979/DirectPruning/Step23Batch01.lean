import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step23Batch01 (N12Compact.C713Shared.dictionary) [
  plan1396 (11475,(some [113730]),11485) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1397 (11476,(some [113731]),11486) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1398 (11477,(some [113732]),11487) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1399 (11478,(some [113733]),11488) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1400 (11479,(some [113734]),11489) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1401 (11480,(some [113735]),11490) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1402 (11481,(some [113736]),11491) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1403 (11482,(some [113737]),11492) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan1404 empty(11483)]
