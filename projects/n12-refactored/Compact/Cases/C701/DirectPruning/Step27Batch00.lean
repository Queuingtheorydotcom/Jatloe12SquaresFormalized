import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step27Batch00 (N12Compact.C713Shared.dictionary) [
  plan862 (482,none,503) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan863 (483,none,504) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan864 (484,none,505) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan865 (485,none,506) [.direct (.single 0), .direct (.single 1), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 8), .direct (.single 8), .direct (.single 3), .direct (.single 1), .direct (.single 5), .direct (.copy 13)],
  plan866 (486,(some [109133]),507) [.block [.pair 0 5], .block [.pair 0 2], .direct (.pair 1 2), .direct (.single 2), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 2 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 2), .block [.pair 0 2], .direct (.single 4), .direct (.copy 13)],
  plan867 (487,(some [109134]),508) [.block [.pair 0 2], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 13)],
  plan868 (488,(some [109135]),509) [.block [.pair 0 2], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)],
  plan869 (489,(some [109136]),510) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)],
  plan870 (490,(some [109137]),511) [.block [.pair 0 2], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)],
  plan871 (491,(some [109138]),512) [.block [.pair 0 6], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.pair 3 6), .block [.pair 0 7], .block [.pair 0 7], .direct (.single 3), .block [.pair 0 3], .direct (.single 5), .direct (.copy 12)],
  plan872 empty(492),
  plan873 empty(493),
  plan874 empty(494),
  plan875 empty(495),
  plan876 empty(496),
  plan877 empty(497)]
