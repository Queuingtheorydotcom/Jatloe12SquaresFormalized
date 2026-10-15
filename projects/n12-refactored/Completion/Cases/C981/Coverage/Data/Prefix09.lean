import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk000
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk001
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk002
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk003
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk004
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk005
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk006
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk007
import Completion.Cases.C981.Coverage.Data.Prefix09Chunks.Chunk008

namespace S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix09 : List (List (Finset Nat)) :=
  prefix09Chunk000 ++ prefix09Chunk001 ++ prefix09Chunk002 ++ prefix09Chunk003 ++ prefix09Chunk004 ++ prefix09Chunk005 ++ prefix09Chunk006 ++ prefix09Chunk007 ++ prefix09Chunk008
end S12Completion.C981.Coverage
