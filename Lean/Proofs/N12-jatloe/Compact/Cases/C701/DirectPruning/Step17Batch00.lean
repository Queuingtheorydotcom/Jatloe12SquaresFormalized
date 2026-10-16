import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step17Batch00 (N12Compact.C713Shared.dictionary) [
  plan358 (314,(some [84427,108925]),378) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 7, .pair 0 4], .block [.pair 0 9, .pair 0 4], .block [.pair 0 9, .pair 0 9], .direct (.pair 0 8), .direct (.single 9), .direct (.single 9), .block [.pair 0 7, .pair 0 4], .direct (.single 2), .block [.pair 0 9, .pair 0 9], .direct (.copy 14)],
  plan359 empty(315),
  plan360 empty(316),
  plan361 empty(317),
  plan362 empty(318),
  plan363 empty(319),
  plan364 empty(320),
  plan365 empty(321),
  plan366 empty(322),
  plan367 empty(323),
  plan368 empty(324),
  plan369 empty(325),
  plan370 empty(326),
  plan371 (327,(some [108926]),379) [.block [.pair 0 9], .block [.pair 0 4], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.pair 6 8), .block [.pair 0 9], .block [.pair 0 9], .block [.pair 0 6], .block [.pair 0 9], .direct (.single 6), .direct (.copy 14)],
  plan372 (328,(some [108927]),380) [.block [.pair 0 9], .block [.pair 0 4], .block [.pair 0 6], .direct (.pair 5 6), .direct (.single 6), .direct (.single 7), .direct (.pair 4 8), .block [.pair 0 9], .block [.pair 0 9], .block [.pair 0 6], .block [.pair 0 9], .direct (.single 6), .direct (.copy 14)],
  plan373 (329,(some [108928]),381) [.block [.pair 0 8], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.pair 3 7), .block [.pair 0 8], .block [.pair 0 8], .block [.pair 0 5], .block [.pair 0 8], .direct (.single 5), .direct (.copy 13)]]
