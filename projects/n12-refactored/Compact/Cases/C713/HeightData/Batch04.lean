import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry32 : Entry :=
  ⟨⟨3220, ⟨0,100000000,-195007693,false⟩, some 3327⟩,
   ⟨(103/73),(21007693/100000000)⟩⟩

private def base32 : List Row :=
  materialize_rows% (entry32.spec.base C713Shared.dictionary)
private def target32 : List Row :=
  materialize_rows% (entry32.spec.targets C713Shared.dictionary)

private theorem base32_exact :
    base32 = entry32.spec.base C713Shared.dictionary := by decide +kernel
private theorem target32_exact :
    target32 = entry32.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric32 :
    PlanarVertexSparse.UnorderedCheck base32 [] target32 := by decide +kernel

theorem entry32_checked : entry32.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base32_exact, ← target32_exact] using numeric32
  · change entry32.TargetCheck
    decide +kernel

def entry33 : Entry :=
  ⟨⟨3221, ⟨0,100000000,-194900273,false⟩, some 3328⟩,
   ⟨(26527/18785),(20900273/100000000)⟩⟩

private def base33 : List Row :=
  materialize_rows% (entry33.spec.base C713Shared.dictionary)
private def target33 : List Row :=
  materialize_rows% (entry33.spec.targets C713Shared.dictionary)

private theorem base33_exact :
    base33 = entry33.spec.base C713Shared.dictionary := by decide +kernel
private theorem target33_exact :
    target33 = entry33.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric33 :
    PlanarVertexSparse.UnorderedCheck base33 [] target33 := by decide +kernel

theorem entry33_checked : entry33.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base33_exact, ← target33_exact] using numeric33
  · change entry33.TargetCheck
    decide +kernel

def entry34 : Entry :=
  ⟨⟨3222, ⟨0,100000000,-194817159,false⟩, some 3329⟩,
   ⟨(6671/4721),(20817159/100000000)⟩⟩

private def base34 : List Row :=
  materialize_rows% (entry34.spec.base C713Shared.dictionary)
private def target34 : List Row :=
  materialize_rows% (entry34.spec.targets C713Shared.dictionary)

private theorem base34_exact :
    base34 = entry34.spec.base C713Shared.dictionary := by decide +kernel
private theorem target34_exact :
    target34 = entry34.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric34 :
    PlanarVertexSparse.UnorderedCheck base34 [] target34 := by decide +kernel

theorem entry34_checked : entry34.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base34_exact, ← target34_exact] using numeric34
  · change entry34.TargetCheck
    decide +kernel

def entry35 : Entry :=
  ⟨⟨3223, ⟨0,10000000,-19475807,false⟩, some 3330⟩,
   ⟨(26839/18985),(2075807/10000000)⟩⟩

private def base35 : List Row :=
  materialize_rows% (entry35.spec.base C713Shared.dictionary)
private def target35 : List Row :=
  materialize_rows% (entry35.spec.targets C713Shared.dictionary)

private theorem base35_exact :
    base35 = entry35.spec.base C713Shared.dictionary := by decide +kernel
private theorem target35_exact :
    target35 = entry35.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric35 :
    PlanarVertexSparse.UnorderedCheck base35 [] target35 := by decide +kernel

theorem entry35_checked : entry35.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base35_exact, ← target35_exact] using numeric35
  · change entry35.TargetCheck
    decide +kernel

def entry36 : Entry :=
  ⟨⟨3224, ⟨0,100000000,-194722691,false⟩, some 3331⟩,
   ⟨(1687/1193),(20722691/100000000)⟩⟩

private def base36 : List Row :=
  materialize_rows% (entry36.spec.base C713Shared.dictionary)
private def target36 : List Row :=
  materialize_rows% (entry36.spec.targets C713Shared.dictionary)

private theorem base36_exact :
    base36 = entry36.spec.base C713Shared.dictionary := by decide +kernel
private theorem target36_exact :
    target36 = entry36.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric36 :
    PlanarVertexSparse.UnorderedCheck base36 [] target36 := by decide +kernel

theorem entry36_checked : entry36.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base36_exact, ← target36_exact] using numeric36
  · change entry36.TargetCheck
    decide +kernel

def entry37 : Entry :=
  ⟨⟨3225, ⟨0,50000000,-97355341,false⟩, some 3332⟩,
   ⟨(27143/19193),(10355341/50000000)⟩⟩

private def base37 : List Row :=
  materialize_rows% (entry37.spec.base C713Shared.dictionary)
private def target37 : List Row :=
  materialize_rows% (entry37.spec.targets C713Shared.dictionary)

private theorem base37_exact :
    base37 = entry37.spec.base C713Shared.dictionary := by decide +kernel
private theorem target37_exact :
    target37 = entry37.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric37 :
    PlanarVertexSparse.UnorderedCheck base37 [] target37 := by decide +kernel

theorem entry37_checked : entry37.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base37_exact, ← target37_exact] using numeric37
  · change entry37.TargetCheck
    decide +kernel

def entry38 : Entry :=
  ⟨⟨3226, ⟨0,50000000,-97355319,false⟩, some 3333⟩,
   ⟨(707107/500000),(10355319/50000000)⟩⟩

private def base38 : List Row :=
  materialize_rows% (entry38.spec.base C713Shared.dictionary)
private def target38 : List Row :=
  materialize_rows% (entry38.spec.targets C713Shared.dictionary)

private theorem base38_exact :
    base38 = entry38.spec.base C713Shared.dictionary := by decide +kernel
private theorem target38_exact :
    target38 = entry38.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric38 :
    PlanarVertexSparse.UnorderedCheck base38 [] target38 := by decide +kernel

theorem entry38_checked : entry38.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base38_exact, ← target38_exact] using numeric38
  · change entry38.TargetCheck
    decide +kernel

def entry39 : Entry :=
  ⟨⟨3227, ⟨0,4000000,-7788867,false⟩, some 3334⟩,
   ⟨(6823/4825),(828867/4000000)⟩⟩

private def base39 : List Row :=
  materialize_rows% (entry39.spec.base C713Shared.dictionary)
private def target39 : List Row :=
  materialize_rows% (entry39.spec.targets C713Shared.dictionary)

private theorem base39_exact :
    base39 = entry39.spec.base C713Shared.dictionary := by decide +kernel
private theorem target39_exact :
    target39 = entry39.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric39 :
    PlanarVertexSparse.UnorderedCheck base39 [] target39 := by decide +kernel

theorem entry39_checked : entry39.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base39_exact, ← target39_exact] using numeric39
  · change entry39.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
