import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step13Batch00 (N12Compact.C713Shared.dictionary) [
  plan201 (1577,none,1453) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan202 (1578,none,1454) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan203 (1579,none,1455) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 2), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan204 (1580,none,1456) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 2), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan205 (1581,none,1457) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan206 empty(1582),
  plan207 empty(1583),
  plan208 empty(1584),
  plan209 (1585,(some [108833]),1458) [.block [.pair 0 5], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.pair 2 5), .block [.pair 0 6], .block [.pair 0 6], .direct (.single 3), .block [.pair 0 3], .direct (.single 4), .direct (.copy 11)],
  plan210 (1586,(some [108834]),1459) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)],
  plan211 (1587,(some [108828]),1460) [.block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.pair 3 7), .block [.pair 0 8], .block [.pair 0 8], .direct (.single 4), .block [.pair 0 4], .direct (.single 6), .direct (.copy 13)],
  plan212 (1588,(some [108829]),1461) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 13)],
  plan213 (1589,(some [108830]),1462) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 13)],
  plan214 empty(1590),
  plan215 empty(1591),
  plan216 empty(1592)]
