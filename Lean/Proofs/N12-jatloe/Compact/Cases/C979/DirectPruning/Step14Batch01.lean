import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C979DirectPruning.Step14Batch01 (N12Compact.C713Shared.dictionary) [
  plan622 (11637,none,11730) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan623 (11638,(some [113286]),11731) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan624 (11639,(some [113287]),11732) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan625 (11640,(some [113288]),11733) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan626 (11641,(some [113289]),11734) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan627 (11642,(some [113290]),11735) [.direct (.pair 0 6), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 13)],
  plan628 (11643,(some [113291]),11736) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan629 empty(11644),
  plan630 empty(11645),
  plan631 (11646,(some [113292]),11737) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan632 (11647,(some [113293]),11738) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan633 (11648,(some [113294]),11739) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan634 (11649,(some [113295]),11740) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan635 (11650,(some [113296]),11741) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan636 (11651,(some [113297]),11742) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)],
  plan637 (11652,(some [113298]),11743) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)]]
