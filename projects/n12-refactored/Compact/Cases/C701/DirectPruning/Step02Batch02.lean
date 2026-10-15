import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step02Batch02 (N12Compact.C713Shared.dictionary) [
  plan979 empty(609),
  plan980 (610,(some [112501]),709) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan981 (611,(some [112503]),710) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan982 (612,(some [112505]),711) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan983 (613,(some [112507]),712) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan984 (614,(some [112509]),713) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan985 (615,(some [112511,112512]),714) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 6], .block [.pair 0 6, .pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2, .pair 0 2], .direct (.single 0), .block [.pair 0 6, .pair 0 6], .direct (.copy 10)],
  plan986 (616,(some [112515]),715) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan987 (617,(some [112517]),716) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan988 (618,(some [112519]),717) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan989 (619,(some [112521]),718) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan990 (620,(some [112523]),719) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan991 (621,(some [112525]),720) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan992 (622,(some [112527]),721) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan993 (623,(some [112529]),722) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)],
  plan994 (624,(some [112531]),723) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 5], .block [.pair 0 6], .direct (.single 5), .direct (.single 5), .block [.pair 0 2], .direct (.single 0), .block [.pair 0 6], .direct (.copy 10)]]
