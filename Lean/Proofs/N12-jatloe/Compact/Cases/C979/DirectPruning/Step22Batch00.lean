import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step22Batch00 (N12Compact.C713Shared.dictionary) [
  plan1288 (11367,(some [113704]),11459) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 3], .direct (.single 5), .direct (.single 5), .direct (.single 2), .direct (.single 0), .block [.pair 0 4], .direct (.copy 10)],
  plan1289 (11368,(some [113705]),11460) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 3], .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .block [.pair 0 4], .direct (.copy 11)],
  plan1290 (11369,(some [113706]),11461) [.block [.pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .block [.pair 0 2], .block [.pair 0 4], .direct (.copy 12)],
  plan1291 (11370,(some [113707]),11462) [.block [.pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .block [.pair 0 2], .block [.pair 0 4], .direct (.copy 12)],
  plan1292 (11371,(some [113708]),11463) [.block [.pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 2), .block [.pair 0 2], .block [.pair 0 4], .direct (.copy 12)],
  plan1293 empty(11372),
  plan1294 empty(11373),
  plan1295 empty(11374),
  plan1296 empty(11375),
  plan1297 empty(11376),
  plan1298 empty(11377),
  plan1299 empty(11378),
  plan1300 empty(11379),
  plan1301 empty(11380),
  plan1302 empty(11381),
  plan1303 empty(11382)]
