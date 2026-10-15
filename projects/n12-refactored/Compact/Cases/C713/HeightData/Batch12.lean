import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry96 : Entry :=
  ⟨⟨3284, ⟨0,100000000,-216561943,false⟩, some 3391⟩,
   ⟨(32479/28705),(42561943/100000000)⟩⟩

private def base96 : List Row :=
  materialize_rows% (entry96.spec.base C713Shared.dictionary)
private def target96 : List Row :=
  materialize_rows% (entry96.spec.targets C713Shared.dictionary)

private theorem base96_exact :
    base96 = entry96.spec.base C713Shared.dictionary := by decide +kernel
private theorem target96_exact :
    target96 = entry96.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric96 :
    PlanarVertexSparse.UnorderedCheck base96 [] target96 := by decide +kernel

theorem entry96_checked : entry96.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base96_exact, ← target96_exact] using numeric96
  · change entry96.TargetCheck
    decide +kernel

def entry97 : Entry :=
  ⟨⟨3285, ⟨0,25000000,-54838529,false⟩, some 3392⟩,
   ⟨(32647/30073),(11338529/25000000)⟩⟩

private def base97 : List Row :=
  materialize_rows% (entry97.spec.base C713Shared.dictionary)
private def target97 : List Row :=
  materialize_rows% (entry97.spec.targets C713Shared.dictionary)

private theorem base97_exact :
    base97 = entry97.spec.base C713Shared.dictionary := by decide +kernel
private theorem target97_exact :
    target97 = entry97.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric97 :
    PlanarVertexSparse.UnorderedCheck base97 [] target97 := by decide +kernel

theorem entry97_checked : entry97.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base97_exact, ← target97_exact] using numeric97
  · change entry97.TargetCheck
    decide +kernel

def entry98 : Entry :=
  ⟨⟨3286, ⟨0,100000000,-219803473,false⟩, some 3393⟩,
   ⟨(8167/7577),(45803473/100000000)⟩⟩

private def base98 : List Row :=
  materialize_rows% (entry98.spec.base C713Shared.dictionary)
private def target98 : List Row :=
  materialize_rows% (entry98.spec.targets C713Shared.dictionary)

private theorem base98_exact :
    base98 = entry98.spec.base C713Shared.dictionary := by decide +kernel
private theorem target98_exact :
    target98 = entry98.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric98 :
    PlanarVertexSparse.UnorderedCheck base98 [] target98 := by decide +kernel

theorem entry98_checked : entry98.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base98_exact, ← target98_exact] using numeric98
  · change entry98.TargetCheck
    decide +kernel

def entry99 : Entry :=
  ⟨⟨3287, ⟨0,50000000,-110123907,false⟩, some 3394⟩,
   ⟨(32687/30545),(23123907/50000000)⟩⟩

private def base99 : List Row :=
  materialize_rows% (entry99.spec.base C713Shared.dictionary)
private def target99 : List Row :=
  materialize_rows% (entry99.spec.targets C713Shared.dictionary)

private theorem base99_exact :
    base99 = entry99.spec.base C713Shared.dictionary := by decide +kernel
private theorem target99_exact :
    target99 = entry99.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric99 :
    PlanarVertexSparse.UnorderedCheck base99 [] target99 := by decide +kernel

theorem entry99_checked : entry99.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base99_exact, ← target99_exact] using numeric99
  · change entry99.TargetCheck
    decide +kernel

def entry100 : Entry :=
  ⟨⟨3288, ⟨0,20000000,-44137399,false⟩, some 3395⟩,
   ⟨(511/481),(9337399/20000000)⟩⟩

private def base100 : List Row :=
  materialize_rows% (entry100.spec.base C713Shared.dictionary)
private def target100 : List Row :=
  materialize_rows% (entry100.spec.targets C713Shared.dictionary)

private theorem base100_exact :
    base100 = entry100.spec.base C713Shared.dictionary := by decide +kernel
private theorem target100_exact :
    target100 = entry100.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric100 :
    PlanarVertexSparse.UnorderedCheck base100 [] target100 := by decide +kernel

theorem entry100_checked : entry100.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base100_exact, ← target100_exact] using numeric100
  · change entry100.TargetCheck
    decide +kernel

def entry101 : Entry :=
  ⟨⟨3289, ⟨0,100000000,-221120879,false⟩, some 3396⟩,
   ⟨(32719/31025),(47120879/100000000)⟩⟩

private def base101 : List Row :=
  materialize_rows% (entry101.spec.base C713Shared.dictionary)
private def target101 : List Row :=
  materialize_rows% (entry101.spec.targets C713Shared.dictionary)

private theorem base101_exact :
    base101 = entry101.spec.base C713Shared.dictionary := by decide +kernel
private theorem target101_exact :
    target101 = entry101.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric101 :
    PlanarVertexSparse.UnorderedCheck base101 [] target101 := by decide +kernel

theorem entry101_checked : entry101.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base101_exact, ← target101_exact] using numeric101
  · change entry101.TargetCheck
    decide +kernel

def entry102 : Entry :=
  ⟨⟨3290, ⟨0,100000000,-221549337,false⟩, some 3397⟩,
   ⟨(8183/7817),(47549337/100000000)⟩⟩

private def base102 : List Row :=
  materialize_rows% (entry102.spec.base C713Shared.dictionary)
private def target102 : List Row :=
  materialize_rows% (entry102.spec.targets C713Shared.dictionary)

private theorem base102_exact :
    base102 = entry102.spec.base C713Shared.dictionary := by decide +kernel
private theorem target102_exact :
    target102 = entry102.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric102 :
    PlanarVertexSparse.UnorderedCheck base102 [] target102 := by decide +kernel

theorem entry102_checked : entry102.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base102_exact, ← target102_exact] using numeric102
  · change entry102.TargetCheck
    decide +kernel

def entry103 : Entry :=
  ⟨⟨3291, ⟨0,100000000,-221972251,false⟩, none⟩,
   ⟨(32743/31513),(47972251/100000000)⟩⟩

private def base103 : List Row :=
  materialize_rows% (entry103.spec.base C713Shared.dictionary)
private def target103 : List Row :=
  materialize_rows% (entry103.spec.targets C713Shared.dictionary)

private theorem base103_exact :
    base103 = entry103.spec.base C713Shared.dictionary := by decide +kernel
private theorem target103_exact :
    target103 = entry103.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric103 :
    PlanarVertexSparse.UnorderedCheck base103 [] target103 := by decide +kernel

theorem entry103_checked : entry103.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base103_exact, ← target103_exact] using numeric103
  · change entry103.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
