import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C978DirectPruning.Step12Batch02 (N12Compact.C713Shared.dictionary) [
  plan160 (7897,(some [112681]),7961) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 2 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .direct (.single 3), .direct (.copy 11)],
  plan161 (7898,(some [112682]),7962) [.block [.pair 0 4], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 2 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .direct (.single 3), .direct (.copy 11)],
  plan162 (7899,(some [112683]),7963) [.block [.pair 0 4], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 2 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .direct (.single 3), .direct (.copy 11)],
  plan163 (7900,(some [112684]),7964) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 2 4), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .direct (.single 3), .direct (.copy 11)],
  plan164 (7901,(some [112685]),7965) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 11)],
  plan165 (7902,(some [112686]),7966) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 11)],
  plan166 (7903,(some [112687]),7967) [.block [.pair 0 4], .block [.pair 0 3], .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 11)],
  plan167 (7904,(some [112688]),7968) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 11)],
  plan168 (7905,(some [112690]),7969) [.block [.pair 0 4], .block [.pair 0 3], .direct (.single 2), .direct (.pair 1 3), .block [.pair 0 4], .block [.pair 0 4], .block [.pair 0 4], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 4], .direct (.copy 11)],
  plan169 empty(7906),
  plan170 empty(7907),
  plan171 empty(7908),
  plan172 empty(7909),
  plan173 (7910,(some [112691]),7970) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.copy 12)],
  plan174 (7911,(some [112692]),7971) [.block [.pair 0 2], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.copy 12)],
  plan175 (7912,(some [112693]),7972) [.block [.pair 0 5], .block [.pair 0 3], .direct (.single 2), .direct (.single 3), .direct (.pair 1 4), .block [.pair 0 5], .block [.pair 0 5], .block [.pair 0 5], .direct (.single 2), .block [.pair 0 3], .block [.pair 0 5], .direct (.copy 12)]]
