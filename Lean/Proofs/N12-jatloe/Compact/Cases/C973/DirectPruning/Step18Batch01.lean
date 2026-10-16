import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step18Batch01 (N12Compact.C713Shared.dictionary) [
  plan400 (16,(some [95752,95751,95750,111621]),5922) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 3, .pair 0 2, .pair 0 2], .block [.pair 0 3, .pair 0 3, .pair 0 2, .pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .direct (.single 1), .direct (.single 0), .block [.pair 0 3, .pair 0 3, .pair 0 2, .pair 0 2], .direct (.copy 10)],
  plan401 (17,(some [95758,95757,111622]),5923) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3, .pair 0 2, .pair 0 2], .block [.pair 0 3, .pair 0 2, .pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .direct (.single 1), .direct (.single 0), .block [.pair 0 3, .pair 0 2, .pair 0 2], .direct (.copy 10)],
  plan402 (18,(some [111623]),5924) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 1), .direct (.single 0), .block [.pair 0 2], .direct (.copy 10)],
  plan403 empty(19),
  plan404 empty(20),
  plan405 empty(21),
  plan406 empty(22),
  plan407 (23,(some [111625]),5925) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan408 (24,(some [111626]),5926) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan409 (25,(some [111627]),5927) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan410 (26,(some [111628]),5928) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan411 (27,(some [111629]),5929) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan412 (28,(some [111630]),5930) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan413 (29,(some [111631]),5931) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 5], .direct (.copy 10)],
  plan414 (30,(some [95771,111632]),5932) [.direct (.single 0), .block [.pair 0 1, .pair 0 1], .block [.pair 0 1, .pair 0 5], .block [.pair 0 5, .pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1, .pair 0 1], .direct (.single 0), .block [.pair 0 5, .pair 0 5], .direct (.copy 10)],
  plan415 (31,(some [95776,95775,95774,111633]),5933) [.direct (.single 0), .block [.pair 0 1, .pair 0 1, .pair 0 1, .pair 0 1], .block [.pair 0 1, .pair 0 1, .pair 0 1, .pair 0 5], .block [.pair 0 5, .pair 0 5, .pair 0 5, .pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 5), .block [.pair 0 1, .pair 0 1, .pair 0 1, .pair 0 1], .direct (.single 0), .block [.pair 0 5, .pair 0 5, .pair 0 5, .pair 0 5], .direct (.copy 10)]]
