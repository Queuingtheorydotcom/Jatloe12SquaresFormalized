import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C973DirectPruning.Step02Batch01 (N12Compact.C713Shared.dictionary) [
  plan922 empty(1638),
  plan923 empty(1639),
  plan924 empty(1640),
  plan925 empty(1641),
  plan926 empty(1642),
  plan927 empty(1643),
  plan928 empty(1644),
  plan929 empty(1645),
  plan930 empty(1646),
  plan931 empty(1647),
  plan932 (1648,(some [111167]),7768) [.direct (.pair 0 5), .block [.pair 0 1], .block [.pair 0 5], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5], .block [.pair 0 5], .direct (.single 5), .direct (.copy 11)],
  plan933 (1649,(some [111169,111170]),7769) [.block [.pair 0 7, .pair 0 5], .block [.pair 0 5, .pair 0 5], .block [.pair 0 5, .pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 6), .block [.pair 0 5, .pair 0 5], .block [.pair 0 5, .pair 0 5], .direct (.single 5), .direct (.copy 11)],
  plan934 (1650,(some [111173,111174,111175,111176,111177,111178,111179,111180,111181]),7770) [.block [.pair 0 7, .pair 0 7, .pair 0 1, .pair 0 1, .pair 0 1, .pair 0 2, .pair 0 2, .pair 0 3, .pair 0 3], .block [.pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 6), .direct (.single 3), .block [.pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3, .pair 0 3], .direct (.single 5), .direct (.copy 11)],
  plan935 (1651,(some [111191,111192,111193,111194,111195,111196,111197,111198]),7771) [.block [.pair 0 8, .pair 0 8, .pair 0 8, .pair 0 1, .pair 0 1, .pair 0 1, .pair 0 2, .pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 4), .direct (.single 2), .direct (.single 6), .direct (.copy 12)],
  plan936 (1652,(some [111211,111212,111213,111214,111215,111216]),7772) [.block [.pair 0 8, .pair 0 8, .pair 0 8, .pair 0 1, .pair 0 2, .pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 4), .direct (.single 2), .direct (.single 6), .direct (.copy 12)],
  plan937 (1653,(some [111223,111224,111225,111226,111227]),7773) [.block [.pair 0 8, .pair 0 8, .pair 0 1, .pair 0 1, .pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 4), .direct (.single 2), .direct (.single 6), .direct (.copy 12)]]
