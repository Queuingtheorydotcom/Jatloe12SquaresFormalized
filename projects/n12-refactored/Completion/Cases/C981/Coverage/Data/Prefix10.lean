import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk000
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk001
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk002
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk003
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk004
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk005
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk006
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk007
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk008
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk009
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk010
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk011
import Completion.Cases.C981.Coverage.Data.Prefix10Chunks.Chunk012

namespace S12Completion.C981.Coverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix10 : List (List (Finset Nat)) :=
  prefix10Chunk000 ++ prefix10Chunk001 ++ prefix10Chunk002 ++ prefix10Chunk003 ++ prefix10Chunk004 ++ prefix10Chunk005 ++ prefix10Chunk006 ++ prefix10Chunk007 ++ prefix10Chunk008 ++ prefix10Chunk009 ++ prefix10Chunk010 ++ prefix10Chunk011 ++ prefix10Chunk012
end S12Completion.C981.Coverage
