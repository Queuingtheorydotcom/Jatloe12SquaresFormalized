import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step06Batch00 (N12Compact.C713Shared.dictionary) [
  plan1486 (5275,(some [110951]),5403) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 5], .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 4), .direct (.single 1), .block [.pair 0 5], .direct (.copy 13)],
  plan1487 (5276,(some [110976]),5404) [.block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 5], .block [.pair 0 3], .block [.pair 0 3], .direct (.single 4), .block [.pair 0 3], .block [.pair 0 6], .direct (.copy 13)],
  plan1488 empty(5277),
  plan1489 empty(5278),
  plan1490 empty(5279),
  plan1491 empty(5280),
  plan1492 empty(5281),
  plan1493 empty(5282),
  plan1494 (5283,(some [111006]),5405) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 3), .direct (.single 2), .block [.pair 0 5], .direct (.copy 12)],
  plan1495 (5284,(some [111017]),5406) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 3), .direct (.single 2), .block [.pair 0 5], .direct (.copy 12)],
  plan1496 (5285,(some [110962]),5407) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 3), .direct (.single 2), .block [.pair 0 5], .direct (.copy 12)],
  plan1497 (5286,(some [110965]),5408) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 3), .direct (.single 2), .block [.pair 0 5], .direct (.copy 12)],
  plan1498 (5287,(some [110968]),5409) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 5], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 4), .direct (.single 2), .block [.pair 0 6], .direct (.copy 13)],
  plan1499 (5288,(some [110969]),5410) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 4), .direct (.single 2), .block [.pair 0 6], .direct (.copy 13)],
  plan1500 (5289,(some [110970]),5411) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 4), .direct (.single 2), .block [.pair 0 6], .direct (.copy 13)],
  plan1501 (5290,(some [110971]),5412) [.direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 2], .block [.pair 0 2], .direct (.single 4), .direct (.single 2), .block [.pair 0 6], .direct (.copy 13)]]
