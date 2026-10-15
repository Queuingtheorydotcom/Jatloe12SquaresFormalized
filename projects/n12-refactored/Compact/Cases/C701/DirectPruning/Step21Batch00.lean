import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step21Batch00 (N12Compact.C713Shared.dictionary) [
  plan590 (641,(some [109039]),686) [.direct (.single 0), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 1], .direct (.single 0), .block [.pair 0 6], .direct (.copy 11)],
  plan591 (642,(some [109040]),687) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 6], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan592 (643,(some [109041]),688) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan593 (644,(some [109042]),689) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan594 (645,(some [109046]),690) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 12)],
  plan595 (646,(some [109047]),691) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 7], .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 7], .direct (.copy 11)],
  plan596 empty(647),
  plan597 empty(648),
  plan598 empty(649),
  plan599 empty(650),
  plan600 empty(651),
  plan601 empty(652),
  plan602 empty(653),
  plan603 empty(654),
  plan604 empty(655),
  plan605 empty(656)]
