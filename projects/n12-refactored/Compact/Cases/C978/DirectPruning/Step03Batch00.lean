import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C978DirectPruning.Step03Batch00 (N12Compact.C713Shared.dictionary) [
  plan366 (1622,(some [101302,112730]),8603) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 1], .block [.pair 0 2, .pair 0 6], .block [.pair 0 6, .pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2, .pair 0 1], .direct (.single 0), .block [.pair 0 6, .pair 0 6], .direct (.copy 12)],
  plan367 (1623,(some [101305,112731]),8604) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 1], .block [.pair 0 2, .pair 0 6], .block [.pair 0 6, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2, .pair 0 1], .direct (.single 0), .block [.pair 0 6, .pair 0 6], .direct (.copy 12)],
  plan368 (1624,(some [112732]),8605) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 12)],
  plan369 (1625,(some [112733]),8606) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 12)],
  plan370 (1626,(some [112734]),8607) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 12)],
  plan371 (1627,(some [112738]),8608) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 12)],
  plan372 (1628,(some [112739]),8609) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan373 (1629,(some [112740]),8610) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan374 (1630,(some [112741]),8611) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan375 (1631,(some [112742]),8612) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .block [.pair 0 9], .direct (.single 8), .direct (.single 8), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 9], .direct (.copy 13)],
  plan376 empty(1632),
  plan377 empty(1633),
  plan378 empty(1634),
  plan379 empty(1635),
  plan380 empty(1636),
  plan381 empty(1637)]
