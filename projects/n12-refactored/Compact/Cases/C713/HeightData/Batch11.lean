import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry88 : Entry :=
  ⟨⟨3276, ⟨0,25000000,-53160111,false⟩, some 3383⟩,
   ⟨(32143/26993),(9660111/25000000)⟩⟩

private def base88 : List Row :=
  materialize_rows% (entry88.spec.base C713Shared.dictionary)
private def target88 : List Row :=
  materialize_rows% (entry88.spec.targets C713Shared.dictionary)

private theorem base88_exact :
    base88 = entry88.spec.base C713Shared.dictionary := by decide +kernel
private theorem target88_exact :
    target88 = entry88.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric88 :
    PlanarVertexSparse.UnorderedCheck base88 [] target88 := by decide +kernel

theorem entry88_checked : entry88.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base88_exact, ← target88_exact] using numeric88
  · change entry88.TargetCheck
    decide +kernel

def entry89 : Entry :=
  ⟨⟨3277, ⟨0,100000000,-213139377,false⟩, some 3384⟩,
   ⟨(503/425),(39139377/100000000)⟩⟩

private def base89 : List Row :=
  materialize_rows% (entry89.spec.base C713Shared.dictionary)
private def target89 : List Row :=
  materialize_rows% (entry89.spec.targets C713Shared.dictionary)

private theorem base89_exact :
    base89 = entry89.spec.base C713Shared.dictionary := by decide +kernel
private theorem target89_exact :
    target89 = entry89.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric89 :
    PlanarVertexSparse.UnorderedCheck base89 [] target89 := by decide +kernel

theorem entry89_checked : entry89.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base89_exact, ← target89_exact] using numeric89
  · change entry89.TargetCheck
    decide +kernel

def entry90 : Entry :=
  ⟨⟨3278, ⟨0,2500000,-5340909,false⟩, some 3385⟩,
   ⟨(32239/27409),(990909/2500000)⟩⟩

private def base90 : List Row :=
  materialize_rows% (entry90.spec.base C713Shared.dictionary)
private def target90 : List Row :=
  materialize_rows% (entry90.spec.targets C713Shared.dictionary)

private theorem base90_exact :
    base90 = entry90.spec.base C713Shared.dictionary := by decide +kernel
private theorem target90_exact :
    target90 = entry90.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric90 :
    PlanarVertexSparse.UnorderedCheck base90 [] target90 := by decide +kernel

theorem entry90_checked : entry90.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base90_exact, ← target90_exact] using numeric90
  · change entry90.TargetCheck
    decide +kernel

def entry91 : Entry :=
  ⟨⟨3279, ⟨0,3125000,-6691597,false⟩, some 3386⟩,
   ⟨(8071/6905),(1254097/3125000)⟩⟩

private def base91 : List Row :=
  materialize_rows% (entry91.spec.base C713Shared.dictionary)
private def target91 : List Row :=
  materialize_rows% (entry91.spec.targets C713Shared.dictionary)

private theorem base91_exact :
    base91 = entry91.spec.base C713Shared.dictionary := by decide +kernel
private theorem target91_exact :
    target91 = entry91.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric91 :
    PlanarVertexSparse.UnorderedCheck base91 [] target91 := by decide +kernel

theorem entry91_checked : entry91.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base91_exact, ← target91_exact] using numeric91
  · change entry91.TargetCheck
    decide +kernel

def entry92 : Entry :=
  ⟨⟨3280, ⟨0,50000000,-107311667,false⟩, some 3387⟩,
   ⟨(32327/27833),(20311667/50000000)⟩⟩

private def base92 : List Row :=
  materialize_rows% (entry92.spec.base C713Shared.dictionary)
private def target92 : List Row :=
  materialize_rows% (entry92.spec.targets C713Shared.dictionary)

private theorem base92_exact :
    base92 = entry92.spec.base C713Shared.dictionary := by decide +kernel
private theorem target92_exact :
    target92 = entry92.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric92 :
    PlanarVertexSparse.UnorderedCheck base92 [] target92 := by decide +kernel

theorem entry92_checked : entry92.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base92_exact, ← target92_exact] using numeric92
  · change entry92.TargetCheck
    decide +kernel

def entry93 : Entry :=
  ⟨⟨3281, ⟨0,50000000,-107556391,false⟩, some 3388⟩,
   ⟨(2023/1753),(20556391/50000000)⟩⟩

private def base93 : List Row :=
  materialize_rows% (entry93.spec.base C713Shared.dictionary)
private def target93 : List Row :=
  materialize_rows% (entry93.spec.targets C713Shared.dictionary)

private theorem base93_exact :
    base93 = entry93.spec.base C713Shared.dictionary := by decide +kernel
private theorem target93_exact :
    target93 = entry93.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric93 :
    PlanarVertexSparse.UnorderedCheck base93 [] target93 := by decide +kernel

theorem entry93_checked : entry93.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base93_exact, ← target93_exact] using numeric93
  · change entry93.TargetCheck
    decide +kernel

def entry94 : Entry :=
  ⟨⟨3282, ⟨0,50000000,-107799597,false⟩, some 3389⟩,
   ⟨(32407/28265),(20799597/50000000)⟩⟩

private def base94 : List Row :=
  materialize_rows% (entry94.spec.base C713Shared.dictionary)
private def target94 : List Row :=
  materialize_rows% (entry94.spec.targets C713Shared.dictionary)

private theorem base94_exact :
    base94 = entry94.spec.base C713Shared.dictionary := by decide +kernel
private theorem target94_exact :
    target94 = entry94.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric94 :
    PlanarVertexSparse.UnorderedCheck base94 [] target94 := by decide +kernel

theorem entry94_checked : entry94.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base94_exact, ← target94_exact] using numeric94
  · change entry94.TargetCheck
    decide +kernel

def entry95 : Entry :=
  ⟨⟨3283, ⟨0,4000000,-8643293,false⟩, some 3390⟩,
   ⟨(8111/7121),(1683293/4000000)⟩⟩

private def base95 : List Row :=
  materialize_rows% (entry95.spec.base C713Shared.dictionary)
private def target95 : List Row :=
  materialize_rows% (entry95.spec.targets C713Shared.dictionary)

private theorem base95_exact :
    base95 = entry95.spec.base C713Shared.dictionary := by decide +kernel
private theorem target95_exact :
    target95 = entry95.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric95 :
    PlanarVertexSparse.UnorderedCheck base95 [] target95 := by decide +kernel

theorem entry95_checked : entry95.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base95_exact, ← target95_exact] using numeric95
  · change entry95.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
