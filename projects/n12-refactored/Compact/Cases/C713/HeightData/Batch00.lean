import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry0 : Entry :=
  ⟨⟨3188, ⟨0,20000000,-44642577,false⟩, none⟩,
   ⟨(16639/16385),(9842577/20000000)⟩⟩

private def base0 : List Row :=
  materialize_rows% (entry0.spec.base C713Shared.dictionary)
private def target0 : List Row :=
  materialize_rows% (entry0.spec.targets C713Shared.dictionary)

private theorem base0_exact :
    base0 = entry0.spec.base C713Shared.dictionary := by decide +kernel
private theorem target0_exact :
    target0 = entry0.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric0 :
    PlanarVertexSparse.UnorderedCheck base0 [] target0 := by decide +kernel

theorem entry0_checked : entry0.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base0_exact, ← target0_exact] using numeric0
  · change entry0.TargetCheck
    decide +kernel

def entry1 : Entry :=
  ⟨⟨3189, ⟨0,50000000,-105455621,false⟩, some 3296⟩,
   ⟨(79/65),(18455621/50000000)⟩⟩

private def base1 : List Row :=
  materialize_rows% (entry1.spec.base C713Shared.dictionary)
private def target1 : List Row :=
  materialize_rows% (entry1.spec.targets C713Shared.dictionary)

private theorem base1_exact :
    base1 = entry1.spec.base C713Shared.dictionary := by decide +kernel
private theorem target1_exact :
    target1 = entry1.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric1 :
    PlanarVertexSparse.UnorderedCheck base1 [] target1 := by decide +kernel

theorem entry1_checked : entry1.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base1_exact, ← target1_exact] using numeric1
  · change entry1.TargetCheck
    decide +kernel

def entry2 : Entry :=
  ⟨⟨3190, ⟨0,50000000,-105060247,false⟩, some 3297⟩,
   ⟨(20447/16673),(18060247/50000000)⟩⟩

private def base2 : List Row :=
  materialize_rows% (entry2.spec.base C713Shared.dictionary)
private def target2 : List Row :=
  materialize_rows% (entry2.spec.targets C713Shared.dictionary)

private theorem base2_exact :
    base2 = entry2.spec.base C713Shared.dictionary := by decide +kernel
private theorem target2_exact :
    target2 = entry2.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric2 :
    PlanarVertexSparse.UnorderedCheck base2 [] target2 := by decide +kernel

theorem entry2_checked : entry2.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base2_exact, ← target2_exact] using numeric2
  · change entry2.TargetCheck
    decide +kernel

def entry3 : Entry :=
  ⟨⟨3191, ⟨0,2000000,-4186813,false⟩, some 3298⟩,
   ⟨(5167/4177),(706813/2000000)⟩⟩

private def base3 : List Row :=
  materialize_rows% (entry3.spec.base C713Shared.dictionary)
private def target3 : List Row :=
  materialize_rows% (entry3.spec.targets C713Shared.dictionary)

private theorem base3_exact :
    base3 = entry3.spec.base C713Shared.dictionary := by decide +kernel
private theorem target3_exact :
    target3 = entry3.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric3 :
    PlanarVertexSparse.UnorderedCheck base3 [] target3 := by decide +kernel

theorem entry3_checked : entry3.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base3_exact, ← target3_exact] using numeric3
  · change entry3.TargetCheck
    decide +kernel

def entry4 : Entry :=
  ⟨⟨3192, ⟨0,25000000,-52143211,false⟩, some 3299⟩,
   ⟨(20887/16745),(8643211/25000000)⟩⟩

private def base4 : List Row :=
  materialize_rows% (entry4.spec.base C713Shared.dictionary)
private def target4 : List Row :=
  materialize_rows% (entry4.spec.targets C713Shared.dictionary)

private theorem base4_exact :
    base4 = entry4.spec.base C713Shared.dictionary := by decide +kernel
private theorem target4_exact :
    target4 = entry4.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric4 :
    PlanarVertexSparse.UnorderedCheck base4 [] target4 := by decide +kernel

theorem entry4_checked : entry4.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base4_exact, ← target4_exact] using numeric4
  · change entry4.TargetCheck
    decide +kernel

def entry5 : Entry :=
  ⟨⟨3193, ⟨0,100000000,-207818171,false⟩, some 3300⟩,
   ⟨(1319/1049),(33818171/100000000)⟩⟩

private def base5 : List Row :=
  materialize_rows% (entry5.spec.base C713Shared.dictionary)
private def target5 : List Row :=
  materialize_rows% (entry5.spec.targets C713Shared.dictionary)

private theorem base5_exact :
    base5 = entry5.spec.base C713Shared.dictionary := by decide +kernel
private theorem target5_exact :
    target5 = entry5.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric5 :
    PlanarVertexSparse.UnorderedCheck base5 [] target5 := by decide +kernel

theorem entry5_checked : entry5.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base5_exact, ← target5_exact] using numeric5
  · change entry5.TargetCheck
    decide +kernel

def entry6 : Entry :=
  ⟨⟨3194, ⟨0,20000000,-41415537,false⟩, some 3301⟩,
   ⟨(21319/16825),(6615537/20000000)⟩⟩

private def base6 : List Row :=
  materialize_rows% (entry6.spec.base C713Shared.dictionary)
private def target6 : List Row :=
  materialize_rows% (entry6.spec.targets C713Shared.dictionary)

private theorem base6_exact :
    base6 = entry6.spec.base C713Shared.dictionary := by decide +kernel
private theorem target6_exact :
    target6 = entry6.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric6 :
    PlanarVertexSparse.UnorderedCheck base6 [] target6 := by decide +kernel

theorem entry6_checked : entry6.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base6_exact, ← target6_exact] using numeric6
  · change entry6.TargetCheck
    decide +kernel

def entry7 : Entry :=
  ⟨⟨3195, ⟨0,25000000,-51588099,false⟩, some 3302⟩,
   ⟨(5383/4217),(8088099/25000000)⟩⟩

private def base7 : List Row :=
  materialize_rows% (entry7.spec.base C713Shared.dictionary)
private def target7 : List Row :=
  materialize_rows% (entry7.spec.targets C713Shared.dictionary)

private theorem base7_exact :
    base7 = entry7.spec.base C713Shared.dictionary := by decide +kernel
private theorem target7_exact :
    target7 = entry7.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric7 :
    PlanarVertexSparse.UnorderedCheck base7 [] target7 := by decide +kernel

theorem entry7_checked : entry7.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base7_exact, ← target7_exact] using numeric7
  · change entry7.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
