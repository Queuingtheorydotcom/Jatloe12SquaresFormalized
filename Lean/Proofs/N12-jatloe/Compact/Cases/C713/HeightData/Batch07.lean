import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry56 : Entry :=
  ⟨⟨3244, ⟨0,100000000,-197974853,false⟩, some 3351⟩,
   ⟨(29519/21425),(23974853/100000000)⟩⟩

private def base56 : List Row :=
  materialize_rows% (entry56.spec.base C713Shared.dictionary)
private def target56 : List Row :=
  materialize_rows% (entry56.spec.targets C713Shared.dictionary)

private theorem base56_exact :
    base56 = entry56.spec.base C713Shared.dictionary := by decide +kernel
private theorem target56_exact :
    target56 = entry56.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric56 :
    PlanarVertexSparse.UnorderedCheck base56 [] target56 := by decide +kernel

theorem entry56_checked : entry56.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base56_exact, ← target56_exact] using numeric56
  · change entry56.TargetCheck
    decide +kernel

def entry57 : Entry :=
  ⟨⟨3245, ⟨0,50000000,-99158027,false⟩, some 3352⟩,
   ⟨(463/337),(12158027/50000000)⟩⟩

private def base57 : List Row :=
  materialize_rows% (entry57.spec.base C713Shared.dictionary)
private def target57 : List Row :=
  materialize_rows% (entry57.spec.targets C713Shared.dictionary)

private theorem base57_exact :
    base57 = entry57.spec.base C713Shared.dictionary := by decide +kernel
private theorem target57_exact :
    target57 = entry57.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric57 :
    PlanarVertexSparse.UnorderedCheck base57 [] target57 := by decide +kernel

theorem entry57_checked : entry57.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base57_exact, ← target57_exact] using numeric57
  · change entry57.TargetCheck
    decide +kernel

def entry58 : Entry :=
  ⟨⟨3246, ⟨0,12500000,-24833783,false⟩, some 3353⟩,
   ⟨(29743/21713),(3083783/12500000)⟩⟩

private def base58 : List Row :=
  materialize_rows% (entry58.spec.base C713Shared.dictionary)
private def target58 : List Row :=
  materialize_rows% (entry58.spec.targets C713Shared.dictionary)

private theorem base58_exact :
    base58 = entry58.spec.base C713Shared.dictionary := by decide +kernel
private theorem target58_exact :
    target58 = entry58.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric58 :
    PlanarVertexSparse.UnorderedCheck base58 [] target58 := by decide +kernel

theorem entry58_checked : entry58.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base58_exact, ← target58_exact] using numeric58
  · change entry58.TargetCheck
    decide +kernel

def entry59 : Entry :=
  ⟨⟨3247, ⟨0,20000000,-39807379,false⟩, some 3354⟩,
   ⟨(7463/5465),(5007379/20000000)⟩⟩

private def base59 : List Row :=
  materialize_rows% (entry59.spec.base C713Shared.dictionary)
private def target59 : List Row :=
  materialize_rows% (entry59.spec.targets C713Shared.dictionary)

private theorem base59_exact :
    base59 = entry59.spec.base C713Shared.dictionary := by decide +kernel
private theorem target59_exact :
    target59 = entry59.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric59 :
    PlanarVertexSparse.UnorderedCheck base59 [] target59 := by decide +kernel

theorem entry59_checked : entry59.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base59_exact, ← target59_exact] using numeric59
  · change entry59.TargetCheck
    decide +kernel

def entry60 : Entry :=
  ⟨⟨3248, ⟨0,100000000,-199415361,false⟩, some 3355⟩,
   ⟨(29959/22009),(25415361/100000000)⟩⟩

private def base60 : List Row :=
  materialize_rows% (entry60.spec.base C713Shared.dictionary)
private def target60 : List Row :=
  materialize_rows% (entry60.spec.targets C713Shared.dictionary)

private theorem base60_exact :
    base60 = entry60.spec.base C713Shared.dictionary := by decide +kernel
private theorem target60_exact :
    target60 = entry60.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric60 :
    PlanarVertexSparse.UnorderedCheck base60 [] target60 := by decide +kernel

theorem entry60_checked : entry60.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base60_exact, ← target60_exact] using numeric60
  · change entry60.TargetCheck
    decide +kernel

def entry61 : Entry :=
  ⟨⟨3249, ⟨0,2500000,-4995127,false⟩, some 3356⟩,
   ⟨(1879/1385),(645127/2500000)⟩⟩

private def base61 : List Row :=
  materialize_rows% (entry61.spec.base C713Shared.dictionary)
private def target61 : List Row :=
  materialize_rows% (entry61.spec.targets C713Shared.dictionary)

private theorem base61_exact :
    base61 = entry61.spec.base C713Shared.dictionary := by decide +kernel
private theorem target61_exact :
    target61 = entry61.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric61 :
    PlanarVertexSparse.UnorderedCheck base61 [] target61 := by decide +kernel

theorem entry61_checked : entry61.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base61_exact, ← target61_exact] using numeric61
  · change entry61.TargetCheck
    decide +kernel

def entry62 : Entry :=
  ⟨⟨3250, ⟨0,3125000,-6256421,false⟩, some 3357⟩,
   ⟨(30167/22313),(818921/3125000)⟩⟩

private def base62 : List Row :=
  materialize_rows% (entry62.spec.base C713Shared.dictionary)
private def target62 : List Row :=
  materialize_rows% (entry62.spec.targets C713Shared.dictionary)

private theorem base62_exact :
    base62 = entry62.spec.base C713Shared.dictionary := by decide +kernel
private theorem target62_exact :
    target62 = entry62.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric62 :
    PlanarVertexSparse.UnorderedCheck base62 [] target62 := by decide +kernel

theorem entry62_checked : entry62.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base62_exact, ← target62_exact] using numeric62
  · change entry62.TargetCheck
    decide +kernel

def entry63 : Entry :=
  ⟨⟨3251, ⟨0,50000000,-100307981,false⟩, some 3358⟩,
   ⟨(7567/5617),(13307981/50000000)⟩⟩

private def base63 : List Row :=
  materialize_rows% (entry63.spec.base C713Shared.dictionary)
private def target63 : List Row :=
  materialize_rows% (entry63.spec.targets C713Shared.dictionary)

private theorem base63_exact :
    base63 = entry63.spec.base C713Shared.dictionary := by decide +kernel
private theorem target63_exact :
    target63 = entry63.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric63 :
    PlanarVertexSparse.UnorderedCheck base63 [] target63 := by decide +kernel

theorem entry63_checked : entry63.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base63_exact, ← target63_exact] using numeric63
  · change entry63.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
