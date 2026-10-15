import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step22Batch03 (N12Compact.C713Shared.dictionary) [
  plan1336 empty(11415),
  plan1337 empty(11416),
  plan1338 empty(11417),
  plan1339 empty(11418),
  plan1340 empty(11419),
  plan1341 empty(11420),
  plan1342 empty(11421),
  plan1343 empty(11422),
  plan1344 empty(11423),
  plan1345 empty(11424),
  plan1346 empty(11425),
  plan1347 (11426,(some [113709]),11464) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 2), .direct (.single 1), .block [.pair 0 4], .direct (.copy 11)],
  plan1348 (11427,(some [113710]),11465) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan1349 (11428,(some [113711]),11466) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan1350 (11429,(some [113712]),11467) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)],
  plan1351 (11430,(some [113713]),11468) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.pair 0 4), .block [.pair 0 5], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 5], .direct (.copy 12)]]
