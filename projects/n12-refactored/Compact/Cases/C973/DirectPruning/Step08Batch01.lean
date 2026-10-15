import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step08Batch01 (N12Compact.C713Shared.dictionary) [
  plan1301 (7602,(some [99902,112243]),7717) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.pair 0 3), .block [.pair 0 4, .pair 0 3], .block [.pair 0 4, .pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4, .pair 0 3], .direct (.single 1), .direct (.single 6), .direct (.copy 12)],
  plan1302 (7603,(some [112244]),7718) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 3], .direct (.single 1), .direct (.single 5), .direct (.copy 11)],
  plan1303 (7604,(some [112245]),7719) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 3], .direct (.single 1), .direct (.single 5), .direct (.copy 11)],
  plan1304 (7605,(some [112246]),7720) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 2], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 3], .direct (.single 1), .direct (.single 5), .direct (.copy 11)],
  plan1305 (7606,(some [112247]),7721) [.direct (.single 0), .direct (.single 1), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.pair 0 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 3], .direct (.single 1), .direct (.single 5), .direct (.copy 11)],
  plan1306 empty(7607),
  plan1307 empty(7608),
  plan1308 empty(7609),
  plan1309 empty(7610),
  plan1310 empty(7611),
  plan1311 empty(7612),
  plan1312 empty(7613),
  plan1313 empty(7614),
  plan1314 empty(7615),
  plan1315 empty(7616),
  plan1316 (7617,(some [112248]),7722) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 6], .direct (.pair 0 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 6], .block [.pair 0 1], .direct (.single 6), .direct (.copy 12)]]
