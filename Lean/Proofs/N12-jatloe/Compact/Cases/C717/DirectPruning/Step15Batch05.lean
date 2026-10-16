import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C717DirectPruning.Step15Batch05 (N12Compact.C713Shared.dictionary) [
  plan685 empty(4827),
  plan686 empty(4828),
  plan687 empty(4829),
  plan688 empty(4830),
  plan689 empty(4831),
  plan690 empty(4832),
  plan691 empty(4833),
  plan692 empty(4834),
  plan693 empty(4835),
  plan694 empty(4836),
  plan695 empty(4837),
  plan696 empty(4838),
  plan697 empty(4839),
  plan698 (4840,(some [110474]),4705) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 4), .direct (.copy 11)],
  plan699 (4841,(some [110475]),4706) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 4), .direct (.copy 11)],
  plan700 (4842,(some [110476]),4707) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 4], .block [.pair 0 5], .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 4), .direct (.copy 11)]]
