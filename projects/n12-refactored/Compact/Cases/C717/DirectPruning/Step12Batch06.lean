import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step12Batch06 (N12Compact.C713Shared.dictionary) [
  plan356 empty(5881),
  plan357 empty(5882),
  plan358 empty(5883),
  plan359 (5884,(some [110218]),5905) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 2], .direct (.single 0), .block [.pair 0 2], .direct (.copy 13)],
  plan360 (5885,(some [110200]),5906) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 13)],
  plan361 (5886,(some [110201]),5907) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 2], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 13)],
  plan362 (5887,(some [110202]),5908) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 2], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 13)],
  plan363 (5888,(some [110203]),5909) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 2], .direct (.pair 0 7), .direct (.single 8), .direct (.single 8), .block [.pair 0 3], .direct (.single 0), .block [.pair 0 3], .direct (.copy 13)]]
