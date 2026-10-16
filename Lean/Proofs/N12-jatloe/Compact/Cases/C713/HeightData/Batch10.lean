import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry80 : Entry :=
  ⟨⟨3268, ⟨0,50000000,-104308627,false⟩, some 3375⟩,
   ⟨(31679/25409),(17308627/50000000)⟩⟩

private def base80 : List Row :=
  materialize_rows% (entry80.spec.base C713Shared.dictionary)
private def target80 : List Row :=
  materialize_rows% (entry80.spec.targets C713Shared.dictionary)

private theorem base80_exact :
    base80 = entry80.spec.base C713Shared.dictionary := by decide +kernel
private theorem target80_exact :
    target80 = entry80.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric80 :
    PlanarVertexSparse.UnorderedCheck base80 [] target80 := by decide +kernel

theorem entry80_checked : entry80.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base80_exact, ← target80_exact] using numeric80
  · change entry80.TargetCheck
    decide +kernel

def entry81 : Entry :=
  ⟨⟨3269, ⟨0,625,-1307,false⟩, some 3376⟩,
   ⟨(31/25),(439/1250)⟩⟩

private def base81 : List Row :=
  materialize_rows% (entry81.spec.base C713Shared.dictionary)
private def target81 : List Row :=
  materialize_rows% (entry81.spec.targets C713Shared.dictionary)

private theorem base81_exact :
    base81 = entry81.spec.base C713Shared.dictionary := by decide +kernel
private theorem target81_exact :
    target81 = entry81.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric81 :
    PlanarVertexSparse.UnorderedCheck base81 [] target81 := by decide +kernel

theorem entry81_checked : entry81.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base81_exact, ← target81_exact] using numeric81
  · change entry81.TargetCheck
    decide +kernel

def entry82 : Entry :=
  ⟨⟨3270, ⟨0,25000000,-52405881,false⟩, some 3377⟩,
   ⟨(31807/25793),(8905881/25000000)⟩⟩

private def base82 : List Row :=
  materialize_rows% (entry82.spec.base C713Shared.dictionary)
private def target82 : List Row :=
  materialize_rows% (entry82.spec.targets C713Shared.dictionary)

private theorem base82_exact :
    base82 = entry82.spec.base C713Shared.dictionary := by decide +kernel
private theorem target82_exact :
    target82 = entry82.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric82 :
    PlanarVertexSparse.UnorderedCheck base82 [] target82 := by decide +kernel

theorem entry82_checked : entry82.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base82_exact, ← target82_exact] using numeric82
  · change entry82.TargetCheck
    decide +kernel

def entry83 : Entry :=
  ⟨⟨3271, ⟨0,50000000,-105063723,false⟩, some 3378⟩,
   ⟨(7967/6497),(18063723/50000000)⟩⟩

private def base83 : List Row :=
  materialize_rows% (entry83.spec.base C713Shared.dictionary)
private def target83 : List Row :=
  materialize_rows% (entry83.spec.targets C713Shared.dictionary)

private theorem base83_exact :
    base83 = entry83.spec.base C713Shared.dictionary := by decide +kernel
private theorem target83_exact :
    target83 = entry83.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric83 :
    PlanarVertexSparse.UnorderedCheck base83 [] target83 := by decide +kernel

theorem entry83_checked : entry83.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base83_exact, ← target83_exact] using numeric83
  · change entry83.TargetCheck
    decide +kernel

def entry84 : Entry :=
  ⟨⟨3272, ⟨0,100000000,-210631393,false⟩, some 3379⟩,
   ⟨(31927/26185),(36631393/100000000)⟩⟩

private def base84 : List Row :=
  materialize_rows% (entry84.spec.base C713Shared.dictionary)
private def target84 : List Row :=
  materialize_rows% (entry84.spec.targets C713Shared.dictionary)

private theorem base84_exact :
    base84 = entry84.spec.base C713Shared.dictionary := by decide +kernel
private theorem target84_exact :
    target84 = entry84.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric84 :
    PlanarVertexSparse.UnorderedCheck base84 [] target84 := by decide +kernel

theorem entry84_checked : entry84.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base84_exact, ← target84_exact] using numeric84
  · change entry84.TargetCheck
    decide +kernel

def entry85 : Entry :=
  ⟨⟨3273, ⟨0,100000000,-211135007,false⟩, some 3380⟩,
   ⟨(1999/1649),(37135007/100000000)⟩⟩

private def base85 : List Row :=
  materialize_rows% (entry85.spec.base C713Shared.dictionary)
private def target85 : List Row :=
  materialize_rows% (entry85.spec.targets C713Shared.dictionary)

private theorem base85_exact :
    base85 = entry85.spec.base C713Shared.dictionary := by decide +kernel
private theorem target85_exact :
    target85 = entry85.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric85 :
    PlanarVertexSparse.UnorderedCheck base85 [] target85 := by decide +kernel

theorem entry85_checked : entry85.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base85_exact, ← target85_exact] using numeric85
  · change entry85.TargetCheck
    decide +kernel

def entry86 : Entry :=
  ⟨⟨3274, ⟨0,50000000,-105818971,false⟩, some 3381⟩,
   ⟨(32039/26585),(18818971/50000000)⟩⟩

private def base86 : List Row :=
  materialize_rows% (entry86.spec.base C713Shared.dictionary)
private def target86 : List Row :=
  materialize_rows% (entry86.spec.targets C713Shared.dictionary)

private theorem base86_exact :
    base86 = entry86.spec.base C713Shared.dictionary := by decide +kernel
private theorem target86_exact :
    target86 = entry86.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric86 :
    PlanarVertexSparse.UnorderedCheck base86 [] target86 := by decide +kernel

theorem entry86_checked : entry86.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base86_exact, ← target86_exact] using numeric86
  · change entry86.TargetCheck
    decide +kernel

def entry87 : Entry :=
  ⟨⟨3275, ⟨0,50000000,-106069931,false⟩, some 3382⟩,
   ⟨(8023/6697),(19069931/50000000)⟩⟩

private def base87 : List Row :=
  materialize_rows% (entry87.spec.base C713Shared.dictionary)
private def target87 : List Row :=
  materialize_rows% (entry87.spec.targets C713Shared.dictionary)

private theorem base87_exact :
    base87 = entry87.spec.base C713Shared.dictionary := by decide +kernel
private theorem target87_exact :
    target87 = entry87.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric87 :
    PlanarVertexSparse.UnorderedCheck base87 [] target87 := by decide +kernel

theorem entry87_checked : entry87.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base87_exact, ← target87_exact] using numeric87
  · change entry87.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
