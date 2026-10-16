import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step19Batch01 (N12Compact.C713Shared.dictionary) [
  plan502 empty(144),
  plan503 empty(145),
  plan504 empty(146),
  plan505 empty(147),
  plan506 (148,(some [109022]),183) [.direct (.single 0), .direct (.single 1), .direct (.pair 1 2), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 11)],
  plan507 (149,(some [109023]),184) [.direct (.single 0), .direct (.single 1), .direct (.pair 1 2), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 11)],
  plan508 (150,(some [84664,109024]),185) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan509 (151,(some [84667,109025]),186) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan510 (152,(some [84670,109026]),187) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan511 (153,(some [84673,109027]),188) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan512 (154,(some [84676,109028]),189) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan513 (155,(some [84679,109029]),190) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan514 (156,(some [84682,109030]),191) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .direct (.single 0), .direct (.single 5), .direct (.copy 12)],
  plan515 (157,none,192) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan516 (158,none,193) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)],
  plan517 (159,none,194) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 2), .direct (.single 0), .direct (.single 4), .direct (.copy 11)]]
