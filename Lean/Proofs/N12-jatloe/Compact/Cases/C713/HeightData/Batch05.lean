import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry40 : Entry :=
  ⟨⟨3228, ⟨0,100000000,-194755277,false⟩, some 3335⟩,
   ⟨(27439/19409),(20755277/100000000)⟩⟩

private def base40 : List Row :=
  materialize_rows% (entry40.spec.base C713Shared.dictionary)
private def target40 : List Row :=
  materialize_rows% (entry40.spec.targets C713Shared.dictionary)

private theorem base40_exact :
    base40 = entry40.spec.base C713Shared.dictionary := by decide +kernel
private theorem target40_exact :
    target40 = entry40.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric40 :
    PlanarVertexSparse.UnorderedCheck base40 [] target40 := by decide +kernel

theorem entry40_checked : entry40.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base40_exact, ← target40_exact] using numeric40
  · change entry40.TargetCheck
    decide +kernel

def entry41 : Entry :=
  ⟨⟨3229, ⟨0,1562500,-3043923,false⟩, some 3336⟩,
   ⟨(431/305),(325173/1562500)⟩⟩

private def base41 : List Row :=
  materialize_rows% (entry41.spec.base C713Shared.dictionary)
private def target41 : List Row :=
  materialize_rows% (entry41.spec.targets C713Shared.dictionary)

private theorem base41_exact :
    base41 = entry41.spec.base C713Shared.dictionary := by decide +kernel
private theorem target41_exact :
    target41 = entry41.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric41 :
    PlanarVertexSparse.UnorderedCheck base41 [] target41 := by decide +kernel

theorem entry41_checked : entry41.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base41_exact, ← target41_exact] using numeric41
  · change entry41.TargetCheck
    decide +kernel

def entry42 : Entry :=
  ⟨⟨3230, ⟨0,50000000,-97444311,false⟩, some 3337⟩,
   ⟨(27727/19633),(10444311/50000000)⟩⟩

private def base42 : List Row :=
  materialize_rows% (entry42.spec.base C713Shared.dictionary)
private def target42 : List Row :=
  materialize_rows% (entry42.spec.targets C713Shared.dictionary)

private theorem base42_exact :
    base42 = entry42.spec.base C713Shared.dictionary := by decide +kernel
private theorem target42_exact :
    target42 = entry42.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric42 :
    PlanarVertexSparse.UnorderedCheck base42 [] target42 := by decide +kernel

theorem entry42_checked : entry42.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base42_exact, ← target42_exact] using numeric42
  · change entry42.TargetCheck
    decide +kernel

def entry43 : Entry :=
  ⟨⟨3231, ⟨0,10000000,-19498747,false⟩, some 3338⟩,
   ⟨(6967/4937),(2098747/10000000)⟩⟩

private def base43 : List Row :=
  materialize_rows% (entry43.spec.base C713Shared.dictionary)
private def target43 : List Row :=
  materialize_rows% (entry43.spec.targets C713Shared.dictionary)

private theorem base43_exact :
    base43 = entry43.spec.base C713Shared.dictionary := by decide +kernel
private theorem target43_exact :
    target43 = entry43.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric43 :
    PlanarVertexSparse.UnorderedCheck base43 [] target43 := by decide +kernel

theorem entry43_checked : entry43.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base43_exact, ← target43_exact] using numeric43
  · change entry43.TargetCheck
    decide +kernel

def entry44 : Entry :=
  ⟨⟨3232, ⟨0,50000000,-97553569,false⟩, some 3339⟩,
   ⟨(28007/19865),(10553569/50000000)⟩⟩

private def base44 : List Row :=
  materialize_rows% (entry44.spec.base C713Shared.dictionary)
private def target44 : List Row :=
  materialize_rows% (entry44.spec.targets C713Shared.dictionary)

private theorem base44_exact :
    base44 = entry44.spec.base C713Shared.dictionary := by decide +kernel
private theorem target44_exact :
    target44 = entry44.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric44 :
    PlanarVertexSparse.UnorderedCheck base44 [] target44 := by decide +kernel

theorem entry44_checked : entry44.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base44_exact, ← target44_exact] using numeric44
  · change entry44.TargetCheck
    decide +kernel

def entry45 : Entry :=
  ⟨⟨3233, ⟨0,100000000,-195247133,false⟩, some 3340⟩,
   ⟨(1759/1249),(21247133/100000000)⟩⟩

private def base45 : List Row :=
  materialize_rows% (entry45.spec.base C713Shared.dictionary)
private def target45 : List Row :=
  materialize_rows% (entry45.spec.targets C713Shared.dictionary)

private theorem base45_exact :
    base45 = entry45.spec.base C713Shared.dictionary := by decide +kernel
private theorem target45_exact :
    target45 = entry45.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric45 :
    PlanarVertexSparse.UnorderedCheck base45 [] target45 := by decide +kernel

theorem entry45_checked : entry45.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base45_exact, ← target45_exact] using numeric45
  · change entry45.TargetCheck
    decide +kernel

def entry46 : Entry :=
  ⟨⟨3234, ⟨0,50000000,-97703473,false⟩, some 3341⟩,
   ⟨(28279/20105),(10703473/50000000)⟩⟩

private def base46 : List Row :=
  materialize_rows% (entry46.spec.base C713Shared.dictionary)
private def target46 : List Row :=
  materialize_rows% (entry46.spec.targets C713Shared.dictionary)

private theorem base46_exact :
    base46 = entry46.spec.base C713Shared.dictionary := by decide +kernel
private theorem target46_exact :
    target46 = entry46.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric46 :
    PlanarVertexSparse.UnorderedCheck base46 [] target46 := by decide +kernel

theorem entry46_checked : entry46.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base46_exact, ← target46_exact] using numeric46
  · change entry46.TargetCheck
    decide +kernel

def entry47 : Entry :=
  ⟨⟨3235, ⟨0,50000000,-97793027,false⟩, some 3342⟩,
   ⟨(7103/5057),(10793027/50000000)⟩⟩

private def base47 : List Row :=
  materialize_rows% (entry47.spec.base C713Shared.dictionary)
private def target47 : List Row :=
  materialize_rows% (entry47.spec.targets C713Shared.dictionary)

private theorem base47_exact :
    base47 = entry47.spec.base C713Shared.dictionary := by decide +kernel
private theorem target47_exact :
    target47 = entry47.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric47 :
    PlanarVertexSparse.UnorderedCheck base47 [] target47 := by decide +kernel

theorem entry47_checked : entry47.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base47_exact, ← target47_exact] using numeric47
  · change entry47.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
