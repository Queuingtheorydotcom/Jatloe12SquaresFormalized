import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step11Batch03 (N12Compact.C713Shared.dictionary) [
  plan176 empty(1365),
  plan177 empty(1366),
  plan178 empty(1367),
  plan179 empty(1368),
  plan180 empty(1369),
  plan181 empty(1370),
  plan182 empty(1371),
  plan183 empty(1372),
  plan184 empty(1373),
  plan185 empty(1374),
  plan186 empty(1375),
  plan187 empty(1376),
  plan188 (1377,(some [108818]),1387) [.direct (.pair 1 2), .direct (.pair 0 2), .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 2], .block [.pair 0 3], .block [.pair 0 3], .block [.pair 0 2], .direct (.copy 15)],
  plan189 (1378,(some [84174,108819]),1388) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 1], .block [.pair 0 2, .pair 0 1], .block [.pair 0 2, .pair 0 11], .block [.pair 0 1, .pair 0 11], .direct (.pair 0 10), .direct (.single 11), .direct (.single 11), .block [.pair 0 2, .pair 0 1], .block [.pair 0 2, .pair 0 1], .block [.pair 0 1, .pair 0 11], .direct (.copy 16)],
  plan190 (1379,(some [84178,84177,108820]),1389) [.direct (.single 0), .direct (.pair 0 1), .block [.pair 0 2, .pair 0 2, .pair 0 2], .block [.pair 0 7, .pair 0 2, .pair 0 2], .block [.pair 0 8, .pair 0 2, .pair 0 8], .direct (.pair 0 7), .direct (.single 8), .direct (.single 9), .direct (.single 10), .direct (.single 10), .block [.pair 0 7, .pair 0 2, .pair 0 2], .block [.pair 0 2, .pair 0 2, .pair 0 2], .direct (.single 8), .direct (.copy 15)]]
