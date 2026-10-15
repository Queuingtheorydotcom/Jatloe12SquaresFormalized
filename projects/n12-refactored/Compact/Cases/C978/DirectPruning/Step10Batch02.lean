import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C978DirectPruning.Step10Batch02 (N12Compact.C713Shared.dictionary) [
  plan96 (8285,none,8349) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan97 (8286,none,8350) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 1), .direct (.single 4), .direct (.copy 11)],
  plan98 (8287,(some [112623]),8351) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.copy 11)],
  plan99 empty(8288),
  plan100 empty(8289),
  plan101 empty(8290),
  plan102 empty(8291),
  plan103 (8292,(some [112624]),8352) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan104 (8293,(some [112626]),8353) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan105 (8294,(some [112627]),8354) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan106 (8295,(some [112628]),8355) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan107 (8296,(some [112629]),8356) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan108 (8297,(some [112630]),8357) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan109 (8298,(some [112631]),8358) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan110 (8299,(some [112632]),8359) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)],
  plan111 (8300,(some [112633]),8360) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 3], .direct (.single 1), .block [.pair 0 7], .direct (.copy 12)]]
