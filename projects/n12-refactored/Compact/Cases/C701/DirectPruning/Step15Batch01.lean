import Compact.Bridge.IndexedBlockedTargetSyntax
import Compact.Cases.C713.SharedDictionary
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

checked_blocked_batch N12Compact.C701DirectPruning.Step15Batch01 (N12Compact.C713Shared.dictionary) [
  plan262 (1791,(some [84263,108841]),1850) [.direct (.pair 0 4), .block [.pair 0 1, .pair 0 1], .block [.pair 0 5, .pair 0 1], .block [.pair 0 7, .pair 0 1], .block [.pair 0 7, .pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5, .pair 0 1], .block [.pair 0 1, .pair 0 1], .block [.pair 0 7, .pair 0 7], .direct (.copy 12)],
  plan263 (1792,(some [84266,108842]),1851) [.direct (.pair 0 4), .block [.pair 0 1, .pair 0 1], .block [.pair 0 7, .pair 0 1], .block [.pair 0 7, .pair 0 1], .block [.pair 0 7, .pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 7, .pair 0 1], .block [.pair 0 1, .pair 0 1], .block [.pair 0 7, .pair 0 7], .direct (.copy 12)],
  plan264 (1793,(some [108843]),1852) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 7], .block [.pair 0 7], .direct (.pair 0 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 7], .block [.pair 0 1], .block [.pair 0 7], .direct (.copy 12)],
  plan265 (1794,(some [108844]),1853) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 5], .block [.pair 0 5], .direct (.pair 4 5), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 5], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan266 empty(1795),
  plan267 empty(1796),
  plan268 empty(1797),
  plan269 empty(1798),
  plan270 empty(1799),
  plan271 empty(1800),
  plan272 (1801,(some [108846]),1854) [.direct (.pair 0 3), .block [.pair 0 1], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 0 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan273 (1802,(some [108847]),1855) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan274 (1803,(some [108848]),1856) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan275 (1804,(some [108849]),1857) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 1], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan276 (1805,(some [108851]),1858) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 3], .block [.pair 0 4], .direct (.pair 3 4), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .block [.pair 0 4], .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)],
  plan277 (1806,(some [108852]),1859) [.direct (.pair 0 4), .block [.pair 0 1], .block [.pair 0 3], .direct (.pair 2 3), .direct (.single 3), .direct (.single 4), .direct (.single 5), .direct (.single 6), .direct (.single 7), .direct (.single 7), .direct (.single 3), .block [.pair 0 1], .direct (.single 5), .direct (.copy 12)]]
