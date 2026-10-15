import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C713DirectPruning.Step08Batch02 (N12Compact.C713Shared.dictionary) [
  plan852 (3561,(some [109953]),3674) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan853 (3562,(some [109954]),3675) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan854 (3563,(some [109955]),3676) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan855 (3564,(some [109956]),3677) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan856 (3565,(some [109957]),3678) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan857 (3566,(some [109958]),3679) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan858 (3567,(some [109959]),3680) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan859 (3568,(some [109960]),3681) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan860 (3569,(some [109961]),3682) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan861 (3570,(some [109962]),3683) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan862 (3571,(some [109963]),3684) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 1 5), .block [.pair 0 6], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan863 (3572,(some [109964]),3685) [.direct (.pair 0 1), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.pair 0 5), .block [.pair 0 6], .block [.pair 0 4], .block [.pair 0 1], .block [.pair 0 1], .direct (.single 3), .direct (.single 1), .block [.pair 0 6], .direct (.copy 12)],
  plan864 empty(3573),
  plan865 empty(3574),
  plan866 empty(3575),
  plan867 empty(3576)]
