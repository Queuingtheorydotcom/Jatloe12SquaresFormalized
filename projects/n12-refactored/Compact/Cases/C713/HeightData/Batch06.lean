import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry48 : Entry :=
  ⟨⟨3236, ⟨0,100000000,-195783921,false⟩, some 3343⟩,
   ⟨(28543/20353),(21783921/100000000)⟩⟩

private def base48 : List Row :=
  materialize_rows% (entry48.spec.base C713Shared.dictionary)
private def target48 : List Row :=
  materialize_rows% (entry48.spec.targets C713Shared.dictionary)

private theorem base48_exact :
    base48 = entry48.spec.base C713Shared.dictionary := by decide +kernel
private theorem target48_exact :
    target48 = entry48.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric48 :
    PlanarVertexSparse.UnorderedCheck base48 [] target48 := by decide +kernel

theorem entry48_checked : entry48.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base48_exact, ← target48_exact] using numeric48
  · change entry48.TargetCheck
    decide +kernel

def entry49 : Entry :=
  ⟨⟨3237, ⟨0,25,-49,false⟩, some 3344⟩,
   ⟨(7/5),(11/50)⟩⟩

private def base49 : List Row :=
  materialize_rows% (entry49.spec.base C713Shared.dictionary)
private def target49 : List Row :=
  materialize_rows% (entry49.spec.targets C713Shared.dictionary)

private theorem base49_exact :
    base49 = entry49.spec.base C713Shared.dictionary := by decide +kernel
private theorem target49_exact :
    target49 = entry49.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric49 :
    PlanarVertexSparse.UnorderedCheck base49 [] target49 := by decide +kernel

theorem entry49_checked : entry49.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base49_exact, ← target49_exact] using numeric49
  · change entry49.TargetCheck
    decide +kernel

def entry50 : Entry :=
  ⟨⟨3238, ⟨0,50000000,-98116867,false⟩, some 3345⟩,
   ⟨(28799/20609),(11116867/50000000)⟩⟩

private def base50 : List Row :=
  materialize_rows% (entry50.spec.base C713Shared.dictionary)
private def target50 : List Row :=
  materialize_rows% (entry50.spec.targets C713Shared.dictionary)

private theorem base50_exact :
    base50 = entry50.spec.base C713Shared.dictionary := by decide +kernel
private theorem target50_exact :
    target50 = entry50.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric50 :
    PlanarVertexSparse.UnorderedCheck base50 [] target50 := by decide +kernel

theorem entry50_checked : entry50.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base50_exact, ← target50_exact] using numeric50
  · change entry50.TargetCheck
    decide +kernel

def entry51 : Entry :=
  ⟨⟨3239, ⟨0,100000000,-196484559,false⟩, some 3346⟩,
   ⟨(7231/5185),(22484559/100000000)⟩⟩

private def base51 : List Row :=
  materialize_rows% (entry51.spec.base C713Shared.dictionary)
private def target51 : List Row :=
  materialize_rows% (entry51.spec.targets C713Shared.dictionary)

private theorem base51_exact :
    base51 = entry51.spec.base C713Shared.dictionary := by decide +kernel
private theorem target51_exact :
    target51 = entry51.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric51 :
    PlanarVertexSparse.UnorderedCheck base51 [] target51 := by decide +kernel

theorem entry51_checked : entry51.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base51_exact, ← target51_exact] using numeric51
  · change entry51.TargetCheck
    decide +kernel

def entry52 : Entry :=
  ⟨⟨3240, ⟨0,100000000,-196751903,false⟩, some 3347⟩,
   ⟨(29047/20873),(22751903/100000000)⟩⟩

private def base52 : List Row :=
  materialize_rows% (entry52.spec.base C713Shared.dictionary)
private def target52 : List Row :=
  materialize_rows% (entry52.spec.targets C713Shared.dictionary)

private theorem base52_exact :
    base52 = entry52.spec.base C713Shared.dictionary := by decide +kernel
private theorem target52_exact :
    target52 = entry52.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric52 :
    PlanarVertexSparse.UnorderedCheck base52 [] target52 := by decide +kernel

theorem entry52_checked : entry52.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base52_exact, ← target52_exact] using numeric52
  · change entry52.TargetCheck
    decide +kernel

def entry53 : Entry :=
  ⟨⟨3241, ⟨0,100000000,-197035187,false⟩, some 3348⟩,
   ⟨(1823/1313),(23035187/100000000)⟩⟩

private def base53 : List Row :=
  materialize_rows% (entry53.spec.base C713Shared.dictionary)
private def target53 : List Row :=
  materialize_rows% (entry53.spec.targets C713Shared.dictionary)

private theorem base53_exact :
    base53 = entry53.spec.base C713Shared.dictionary := by decide +kernel
private theorem target53_exact :
    target53 = entry53.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric53 :
    PlanarVertexSparse.UnorderedCheck base53 [] target53 := by decide +kernel

theorem entry53_checked : entry53.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base53_exact, ← target53_exact] using numeric53
  · change entry53.TargetCheck
    decide +kernel

def entry54 : Entry :=
  ⟨⟨3242, ⟨0,12500000,-24666729,false⟩, some 3349⟩,
   ⟨(29287/21145),(2916729/12500000)⟩⟩

private def base54 : List Row :=
  materialize_rows% (entry54.spec.base C713Shared.dictionary)
private def target54 : List Row :=
  materialize_rows% (entry54.spec.targets C713Shared.dictionary)

private theorem base54_exact :
    base54 = entry54.spec.base C713Shared.dictionary := by decide +kernel
private theorem target54_exact :
    target54 = entry54.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric54 :
    PlanarVertexSparse.UnorderedCheck base54 [] target54 := by decide +kernel

theorem entry54_checked : entry54.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base54_exact, ← target54_exact] using numeric54
  · change entry54.TargetCheck
    decide +kernel

def entry55 : Entry :=
  ⟨⟨3243, ⟨0,100000000,-197647249,false⟩, some 3350⟩,
   ⟨(7351/5321),(23647249/100000000)⟩⟩

private def base55 : List Row :=
  materialize_rows% (entry55.spec.base C713Shared.dictionary)
private def target55 : List Row :=
  materialize_rows% (entry55.spec.targets C713Shared.dictionary)

private theorem base55_exact :
    base55 = entry55.spec.base C713Shared.dictionary := by decide +kernel
private theorem target55_exact :
    target55 = entry55.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric55 :
    PlanarVertexSparse.UnorderedCheck base55 [] target55 := by decide +kernel

theorem entry55_checked : entry55.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base55_exact, ← target55_exact] using numeric55
  · change entry55.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
