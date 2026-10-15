import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step19Batch00 (N12Compact.C713Shared.dictionary) [
  plan486 (128,none,168) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 12)],
  plan487 (129,none,169) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 12)],
  plan488 (130,(some [109031]),170) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 7], .direct (.copy 13)],
  plan489 (131,(some [109032]),171) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan490 (132,(some [109033]),172) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan491 (133,(some [109034]),173) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan492 (134,(some [109035]),174) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 11)],
  plan493 (135,(some [109036]),175) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 11)],
  plan494 (136,(some [109037]),176) [.direct (.single 0), .direct (.single 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 1), .block [.pair 0 6], .direct (.copy 11)],
  plan495 (137,(some [109038]),177) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan496 (138,(some [109017]),178) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan497 (139,(some [109018]),179) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan498 (140,(some [109019]),180) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan499 (141,(some [109020]),181) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan500 (142,(some [109021]),182) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan501 empty(143)]
