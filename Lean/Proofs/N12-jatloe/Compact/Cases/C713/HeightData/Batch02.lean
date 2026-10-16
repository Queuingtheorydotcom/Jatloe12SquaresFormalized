import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry16 : Entry :=
  ⟨⟨3204, ⟨0,10000000,-20065257,false⟩, some 3311⟩,
   ⟨(23359/17345),(2665257/10000000)⟩⟩

private def base16 : List Row :=
  materialize_rows% (entry16.spec.base C713Shared.dictionary)
private def target16 : List Row :=
  materialize_rows% (entry16.spec.targets C713Shared.dictionary)

private theorem base16_exact :
    base16 = entry16.spec.base C713Shared.dictionary := by decide +kernel
private theorem target16_exact :
    target16 = entry16.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric16 :
    PlanarVertexSparse.UnorderedCheck base16 [] target16 := by decide +kernel

theorem entry16_checked : entry16.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base16_exact, ← target16_exact] using numeric16
  · change entry16.TargetCheck
    decide +kernel

def entry17 : Entry :=
  ⟨⟨3205, ⟨0,100000000,-200124567,false⟩, some 3312⟩,
   ⟨(23/17),(26124567/100000000)⟩⟩

private def base17 : List Row :=
  materialize_rows% (entry17.spec.base C713Shared.dictionary)
private def target17 : List Row :=
  materialize_rows% (entry17.spec.targets C713Shared.dictionary)

private theorem base17_exact :
    base17 = entry17.spec.base C713Shared.dictionary := by decide +kernel
private theorem target17_exact :
    target17 = entry17.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric17 :
    PlanarVertexSparse.UnorderedCheck base17 [] target17 := by decide +kernel

theorem entry17_checked : entry17.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base17_exact, ← target17_exact] using numeric17
  · change entry17.TargetCheck
    decide +kernel

def entry18 : Entry :=
  ⟨⟨3206, ⟨0,50000000,-99569271,false⟩, some 3313⟩,
   ⟨(5983/4385),(12569271/50000000)⟩⟩

private def base18 : List Row :=
  materialize_rows% (entry18.spec.base C713Shared.dictionary)
private def target18 : List Row :=
  materialize_rows% (entry18.spec.targets C713Shared.dictionary)

private theorem base18_exact :
    base18 = entry18.spec.base C713Shared.dictionary := by decide +kernel
private theorem target18_exact :
    target18 = entry18.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric18 :
    PlanarVertexSparse.UnorderedCheck base18 [] target18 := by decide +kernel

theorem entry18_checked : entry18.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base18_exact, ← target18_exact] using numeric18
  · change entry18.TargetCheck
    decide +kernel

def entry19 : Entry :=
  ⟨⟨3207, ⟨0,100000000,-198681329,false⟩, some 3314⟩,
   ⟨(24119/17609),(24681329/100000000)⟩⟩

private def base19 : List Row :=
  materialize_rows% (entry19.spec.base C713Shared.dictionary)
private def target19 : List Row :=
  materialize_rows% (entry19.spec.targets C713Shared.dictionary)

private theorem base19_exact :
    base19 = entry19.spec.base C713Shared.dictionary := by decide +kernel
private theorem target19_exact :
    target19 = entry19.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric19 :
    PlanarVertexSparse.UnorderedCheck base19 [] target19 := by decide +kernel

theorem entry19_checked : entry19.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base19_exact, ← target19_exact] using numeric19
  · change entry19.TargetCheck
    decide +kernel

def entry20 : Entry :=
  ⟨⟨3208, ⟨0,50000000,-99124219,false⟩, some 3315⟩,
   ⟨(1519/1105),(12124219/50000000)⟩⟩

private def base20 : List Row :=
  materialize_rows% (entry20.spec.base C713Shared.dictionary)
private def target20 : List Row :=
  materialize_rows% (entry20.spec.targets C713Shared.dictionary)

private theorem base20_exact :
    base20 = entry20.spec.base C713Shared.dictionary := by decide +kernel
private theorem target20_exact :
    target20 = entry20.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric20 :
    PlanarVertexSparse.UnorderedCheck base20 [] target20 := by decide +kernel

theorem entry20_checked : entry20.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base20_exact, ← target20_exact] using numeric20
  · change entry20.TargetCheck
    decide +kernel

def entry21 : Entry :=
  ⟨⟨3209, ⟨0,100000000,-197840153,false⟩, some 3316⟩,
   ⟨(24487/17753),(23840153/100000000)⟩⟩

private def base21 : List Row :=
  materialize_rows% (entry21.spec.base C713Shared.dictionary)
private def target21 : List Row :=
  materialize_rows% (entry21.spec.targets C713Shared.dictionary)

private theorem base21_exact :
    base21 = entry21.spec.base C713Shared.dictionary := by decide +kernel
private theorem target21_exact :
    target21 = entry21.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric21 :
    PlanarVertexSparse.UnorderedCheck base21 [] target21 := by decide +kernel

theorem entry21_checked : entry21.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base21_exact, ← target21_exact] using numeric21
  · change entry21.TargetCheck
    decide +kernel

def entry22 : Entry :=
  ⟨⟨3210, ⟨0,100000000,-197456707,false⟩, some 3317⟩,
   ⟨(6167/4457),(23456707/100000000)⟩⟩

private def base22 : List Row :=
  materialize_rows% (entry22.spec.base C713Shared.dictionary)
private def target22 : List Row :=
  materialize_rows% (entry22.spec.targets C713Shared.dictionary)

private theorem base22_exact :
    base22 = entry22.spec.base C713Shared.dictionary := by decide +kernel
private theorem target22_exact :
    target22 = entry22.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric22 :
    PlanarVertexSparse.UnorderedCheck base22 [] target22 := by decide +kernel

theorem entry22_checked : entry22.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base22_exact, ← target22_exact] using numeric22
  · change entry22.TargetCheck
    decide +kernel

def entry23 : Entry :=
  ⟨⟨3211, ⟨0,100000000,-197098287,false⟩, some 3318⟩,
   ⟨(24847/17905),(23098287/100000000)⟩⟩

private def base23 : List Row :=
  materialize_rows% (entry23.spec.base C713Shared.dictionary)
private def target23 : List Row :=
  materialize_rows% (entry23.spec.targets C713Shared.dictionary)

private theorem base23_exact :
    base23 = entry23.spec.base C713Shared.dictionary := by decide +kernel
private theorem target23_exact :
    target23 = entry23.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric23 :
    PlanarVertexSparse.UnorderedCheck base23 [] target23 := by decide +kernel

theorem entry23_checked : entry23.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base23_exact, ← target23_exact] using numeric23
  · change entry23.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
