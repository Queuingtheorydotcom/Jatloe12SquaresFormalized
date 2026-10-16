import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry72 : Entry :=
  ⟨⟨3260, ⟨0,6250000,-12792069,false⟩, some 3367⟩,
   ⟨(31087/23953),(1917069/6250000)⟩⟩

private def base72 : List Row :=
  materialize_rows% (entry72.spec.base C713Shared.dictionary)
private def target72 : List Row :=
  materialize_rows% (entry72.spec.targets C713Shared.dictionary)

private theorem base72_exact :
    base72 = entry72.spec.base C713Shared.dictionary := by decide +kernel
private theorem target72_exact :
    target72 = entry72.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric72 :
    PlanarVertexSparse.UnorderedCheck base72 [] target72 := by decide +kernel

theorem entry72_checked : entry72.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base72_exact, ← target72_exact] using numeric72
  · change entry72.TargetCheck
    decide +kernel

def entry73 : Entry :=
  ⟨⟨3261, ⟨0,25000000,-51288611,false⟩, some 3368⟩,
   ⟨(487/377),(7788611/25000000)⟩⟩

private def base73 : List Row :=
  materialize_rows% (entry73.spec.base C713Shared.dictionary)
private def target73 : List Row :=
  materialize_rows% (entry73.spec.targets C713Shared.dictionary)

private theorem base73_exact :
    base73 = entry73.spec.base C713Shared.dictionary := by decide +kernel
private theorem target73_exact :
    target73 = entry73.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric73 :
    PlanarVertexSparse.UnorderedCheck base73 [] target73 := by decide +kernel

theorem entry73_checked : entry73.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base73_exact, ← target73_exact] using numeric73
  · change entry73.TargetCheck
    decide +kernel

def entry74 : Entry :=
  ⟨⟨3262, ⟨0,100000000,-205640041,false⟩, some 3369⟩,
   ⟨(31247/24305),(31640041/100000000)⟩⟩

private def base74 : List Row :=
  materialize_rows% (entry74.spec.base C713Shared.dictionary)
private def target74 : List Row :=
  materialize_rows% (entry74.spec.targets C713Shared.dictionary)

private theorem base74_exact :
    base74 = entry74.spec.base C713Shared.dictionary := by decide +kernel
private theorem target74_exact :
    target74 = entry74.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric74 :
    PlanarVertexSparse.UnorderedCheck base74 [] target74 := by decide +kernel

theorem entry74_checked : entry74.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base74_exact, ← target74_exact] using numeric74
  · change entry74.TargetCheck
    decide +kernel

def entry75 : Entry :=
  ⟨⟨3263, ⟨0,50000000,-103064711,false⟩, some 3370⟩,
   ⟨(7831/6121),(16064711/50000000)⟩⟩

private def base75 : List Row :=
  materialize_rows% (entry75.spec.base C713Shared.dictionary)
private def target75 : List Row :=
  materialize_rows% (entry75.spec.targets C713Shared.dictionary)

private theorem base75_exact :
    base75 = entry75.spec.base C713Shared.dictionary := by decide +kernel
private theorem target75_exact :
    target75 = entry75.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric75 :
    PlanarVertexSparse.UnorderedCheck base75 [] target75 := by decide +kernel

theorem entry75_checked : entry75.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base75_exact, ← target75_exact] using numeric75
  · change entry75.TargetCheck
    decide +kernel

def entry76 : Entry :=
  ⟨⟨3264, ⟨0,25000000,-51655531,false⟩, some 3371⟩,
   ⟨(31399/24665),(8155531/25000000)⟩⟩

private def base76 : List Row :=
  materialize_rows% (entry76.spec.base C713Shared.dictionary)
private def target76 : List Row :=
  materialize_rows% (entry76.spec.targets C713Shared.dictionary)

private theorem base76_exact :
    base76 = entry76.spec.base C713Shared.dictionary := by decide +kernel
private theorem target76_exact :
    target76 = entry76.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric76 :
    PlanarVertexSparse.UnorderedCheck base76 [] target76 := by decide +kernel

theorem entry76_checked : entry76.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base76_exact, ← target76_exact] using numeric76
  · change entry76.TargetCheck
    decide +kernel

def entry77 : Entry :=
  ⟨⟨3265, ⟨0,25000000,-51779423,false⟩, some 3372⟩,
   ⟨(1967/1553),(8279423/25000000)⟩⟩

private def base77 : List Row :=
  materialize_rows% (entry77.spec.base C713Shared.dictionary)
private def target77 : List Row :=
  materialize_rows% (entry77.spec.targets C713Shared.dictionary)

private theorem base77_exact :
    base77 = entry77.spec.base C713Shared.dictionary := by decide +kernel
private theorem target77_exact :
    target77 = entry77.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric77 :
    PlanarVertexSparse.UnorderedCheck base77 [] target77 := by decide +kernel

theorem entry77_checked : entry77.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base77_exact, ← target77_exact] using numeric77
  · change entry77.TargetCheck
    decide +kernel

def entry78 : Entry :=
  ⟨⟨3266, ⟨0,12500000,-25951961,false⟩, some 3373⟩,
   ⟨(31543/25033),(4201961/12500000)⟩⟩

private def base78 : List Row :=
  materialize_rows% (entry78.spec.base C713Shared.dictionary)
private def target78 : List Row :=
  materialize_rows% (entry78.spec.targets C713Shared.dictionary)

private theorem base78_exact :
    base78 = entry78.spec.base C713Shared.dictionary := by decide +kernel
private theorem target78_exact :
    target78 = entry78.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric78 :
    PlanarVertexSparse.UnorderedCheck base78 [] target78 := by decide +kernel

theorem entry78_checked : entry78.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base78_exact, ← target78_exact] using numeric78
  · change entry78.TargetCheck
    decide +kernel

def entry79 : Entry :=
  ⟨⟨3267, ⟨0,100000000,-208115681,false⟩, some 3374⟩,
   ⟨(7903/6305),(34115681/100000000)⟩⟩

private def base79 : List Row :=
  materialize_rows% (entry79.spec.base C713Shared.dictionary)
private def target79 : List Row :=
  materialize_rows% (entry79.spec.targets C713Shared.dictionary)

private theorem base79_exact :
    base79 = entry79.spec.base C713Shared.dictionary := by decide +kernel
private theorem target79_exact :
    target79 = entry79.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric79 :
    PlanarVertexSparse.UnorderedCheck base79 [] target79 := by decide +kernel

theorem entry79_checked : entry79.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base79_exact, ← target79_exact] using numeric79
  · change entry79.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
