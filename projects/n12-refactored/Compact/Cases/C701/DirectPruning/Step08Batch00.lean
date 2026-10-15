import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step08Batch00 (N12Compact.C713Shared.dictionary) [
  plan1267 (1525,none,1577) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan1268 (1526,none,1578) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan1269 (1527,none,1579) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 2), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1270 (1528,(some [109297]),1580) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1271 (1529,(some [85175,109300]),1581) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4, .pair 0 4], .block [.pair 0 4, .pair 0 1], .block [.pair 0 1, .pair 0 1], .block [.pair 0 1, .pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 4, .pair 0 4], .direct (.copy 11)],
  plan1272 (1530,(some [109302]),1582) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan1273 empty(1531),
  plan1274 empty(1532),
  plan1275 empty(1533),
  plan1276 empty(1534),
  plan1277 empty(1535),
  plan1278 empty(1536),
  plan1279 empty(1537),
  plan1280 (1538,(some [109272]),1583) [.direct (.pair 0 1), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 1), .block [.pair 0 3], .direct (.copy 11)],
  plan1281 (1539,(some [109273]),1584) [.direct (.pair 0 1), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 1), .block [.pair 0 3], .direct (.copy 11)],
  plan1282 (1540,(some [109274]),1585) [.direct (.pair 0 1), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 1), .block [.pair 0 3], .direct (.copy 12)]]
