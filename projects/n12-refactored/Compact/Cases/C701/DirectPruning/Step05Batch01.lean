import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step05Batch01 (N12Compact.C713Shared.dictionary) [
  plan1172 (219,(some [109201]),278) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1173 (220,(some [109202]),279) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .direct (.single 1), .direct (.single 5), .direct (.copy 12)],
  plan1174 (221,(some [109203]),280) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 2], .direct (.single 5), .direct (.copy 12)],
  plan1175 (222,(some [109204]),281) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 4], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 2], .direct (.single 5), .direct (.copy 12)],
  plan1176 (223,(some [109205]),282) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 2], .direct (.single 5), .direct (.copy 12)],
  plan1177 (224,(some [109206]),283) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 2], .direct (.single 5), .direct (.copy 12)],
  plan1178 empty(225),
  plan1179 empty(226),
  plan1180 empty(227),
  plan1181 empty(228),
  plan1182 empty(229),
  plan1183 empty(230),
  plan1184 empty(231),
  plan1185 (232,(some [109207]),284) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1186 (233,(some [109208]),285) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan1187 (234,(some [109209]),286) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 3], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)]]
