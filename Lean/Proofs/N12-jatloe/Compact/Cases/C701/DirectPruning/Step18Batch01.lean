import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step18Batch01 (N12Compact.C713Shared.dictionary) [
  plan438 (80,(some [108984]),144) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 1), .direct (.single 0), .block [.pair 0 3], .direct (.copy 10)],
  plan439 (81,(some [108985]),145) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 1), .direct (.single 0), .block [.pair 0 3], .direct (.copy 10)],
  plan440 (82,(some [108986]),146) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 1), .direct (.single 0), .block [.pair 0 3], .direct (.copy 10)],
  plan441 (83,(some [108987]),147) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 1), .direct (.single 0), .block [.pair 0 3], .direct (.copy 10)],
  plan442 empty(84),
  plan443 empty(85),
  plan444 empty(86),
  plan445 empty(87),
  plan446 empty(88),
  plan447 empty(89),
  plan448 empty(90),
  plan449 empty(91),
  plan450 empty(92),
  plan451 empty(93),
  plan452 empty(94),
  plan453 empty(95)]
