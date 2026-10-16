import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step19Batch01 (N12Compact.C713Shared.dictionary) [
  plan464 (529,none,6390) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 10)],
  plan465 (530,none,6391) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 10)],
  plan466 (531,none,6392) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 5), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 10)],
  plan467 (532,(some [111660]),6393) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan468 (533,(some [111662]),6394) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan469 (534,(some [111663]),6395) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan470 (535,(some [111664]),6396) [.block [.pair 0 6], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan471 (536,(some [111665]),6397) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan472 (537,(some [111666]),6398) [.block [.pair 0 6], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan473 (538,(some [111667]),6399) [.block [.pair 0 6], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan474 (539,(some [111668]),6400) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan475 (540,(some [111669]),6401) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan476 (541,(some [111670]),605) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan477 (542,(some [111671]),606) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan478 (543,(some [111673]),6402) [.block [.pair 0 6], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)],
  plan479 (544,(some [111674]),6403) [.block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 4], .block [.pair 0 6], .direct (.single 4), .direct (.copy 10)]]
