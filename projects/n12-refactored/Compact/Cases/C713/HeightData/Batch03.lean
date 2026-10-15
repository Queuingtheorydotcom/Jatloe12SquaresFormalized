import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry24 : Entry :=
  ⟨⟨3212, ⟨0,20000000,-39353007,false⟩, some 3319⟩,
   ⟨(391/281),(4553007/20000000)⟩⟩

private def base24 : List Row :=
  materialize_rows% (entry24.spec.base C713Shared.dictionary)
private def target24 : List Row :=
  materialize_rows% (entry24.spec.targets C713Shared.dictionary)

private theorem base24_exact :
    base24 = entry24.spec.base C713Shared.dictionary := by decide +kernel
private theorem target24_exact :
    target24 = entry24.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric24 :
    PlanarVertexSparse.UnorderedCheck base24 [] target24 := by decide +kernel

theorem entry24_checked : entry24.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base24_exact, ← target24_exact] using numeric24
  · change entry24.TargetCheck
    decide +kernel

def entry25 : Entry :=
  ⟨⟨3213, ⟨0,12500000,-24557131,false⟩, some 3320⟩,
   ⟨(25199/18065),(2807131/12500000)⟩⟩

private def base25 : List Row :=
  materialize_rows% (entry25.spec.base C713Shared.dictionary)
private def target25 : List Row :=
  materialize_rows% (entry25.spec.targets C713Shared.dictionary)

private theorem base25_exact :
    base25 = entry25.spec.base C713Shared.dictionary := by decide +kernel
private theorem target25_exact :
    target25 = entry25.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric25 :
    PlanarVertexSparse.UnorderedCheck base25 [] target25 := by decide +kernel

theorem entry25_checked : entry25.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base25_exact, ← target25_exact] using numeric25
  · change entry25.TargetCheck
    decide +kernel

def entry26 : Entry :=
  ⟨⟨3214, ⟨0,12500000,-24521797,false⟩, some 3321⟩,
   ⟨(6343/4537),(2771797/12500000)⟩⟩

private def base26 : List Row :=
  materialize_rows% (entry26.spec.base C713Shared.dictionary)
private def target26 : List Row :=
  materialize_rows% (entry26.spec.targets C713Shared.dictionary)

private theorem base26_exact :
    base26 = entry26.spec.base C713Shared.dictionary := by decide +kernel
private theorem target26_exact :
    target26 = entry26.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric26 :
    PlanarVertexSparse.UnorderedCheck base26 [] target26 := by decide +kernel

theorem entry26_checked : entry26.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base26_exact, ← target26_exact] using numeric26
  · change entry26.TargetCheck
    decide +kernel

def entry27 : Entry :=
  ⟨⟨3215, ⟨0,10000000,-19591703,false⟩, some 3322⟩,
   ⟨(25543/18233),(2191703/10000000)⟩⟩

private def base27 : List Row :=
  materialize_rows% (entry27.spec.base C713Shared.dictionary)
private def target27 : List Row :=
  materialize_rows% (entry27.spec.targets C713Shared.dictionary)

private theorem base27_exact :
    base27 = entry27.spec.base C713Shared.dictionary := by decide +kernel
private theorem target27_exact :
    target27 = entry27.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric27 :
    PlanarVertexSparse.UnorderedCheck base27 [] target27 := by decide +kernel

theorem entry27_checked : entry27.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base27_exact, ← target27_exact] using numeric27
  · change entry27.TargetCheck
    decide +kernel

def entry28 : Entry :=
  ⟨⟨3216, ⟨0,100000000,-195684979,false⟩, some 3323⟩,
   ⟨(1607/1145),(21684979/100000000)⟩⟩

private def base28 : List Row :=
  materialize_rows% (entry28.spec.base C713Shared.dictionary)
private def target28 : List Row :=
  materialize_rows% (entry28.spec.targets C713Shared.dictionary)

private theorem base28_exact :
    base28 = entry28.spec.base C713Shared.dictionary := by decide +kernel
private theorem target28_exact :
    target28 = entry28.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric28 :
    PlanarVertexSparse.UnorderedCheck base28 [] target28 := by decide +kernel

theorem entry28_checked : entry28.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base28_exact, ← target28_exact] using numeric28
  · change entry28.TargetCheck
    decide +kernel

def entry29 : Entry :=
  ⟨⟨3217, ⟨0,100000000,-195478149,false⟩, some 3324⟩,
   ⟨(25879/18409),(21478149/100000000)⟩⟩

private def base29 : List Row :=
  materialize_rows% (entry29.spec.base C713Shared.dictionary)
private def target29 : List Row :=
  materialize_rows% (entry29.spec.targets C713Shared.dictionary)

private theorem base29_exact :
    base29 = entry29.spec.base C713Shared.dictionary := by decide +kernel
private theorem target29_exact :
    target29 = entry29.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric29 :
    PlanarVertexSparse.UnorderedCheck base29 [] target29 := by decide +kernel

theorem entry29_checked : entry29.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base29_exact, ← target29_exact] using numeric29
  · change entry29.TargetCheck
    decide +kernel

def entry30 : Entry :=
  ⟨⟨3218, ⟨0,10000000,-19529643,false⟩, some 3325⟩,
   ⟨(6511/4625),(2129643/10000000)⟩⟩

private def base30 : List Row :=
  materialize_rows% (entry30.spec.base C713Shared.dictionary)
private def target30 : List Row :=
  materialize_rows% (entry30.spec.targets C713Shared.dictionary)

private theorem base30_exact :
    base30 = entry30.spec.base C713Shared.dictionary := by decide +kernel
private theorem target30_exact :
    target30 = entry30.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric30 :
    PlanarVertexSparse.UnorderedCheck base30 [] target30 := by decide +kernel

theorem entry30_checked : entry30.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base30_exact, ← target30_exact] using numeric30
  · change entry30.TargetCheck
    decide +kernel

def entry31 : Entry :=
  ⟨⟨3219, ⟨0,100000000,-195139673,false⟩, some 3326⟩,
   ⟨(26207/18593),(21139673/100000000)⟩⟩

private def base31 : List Row :=
  materialize_rows% (entry31.spec.base C713Shared.dictionary)
private def target31 : List Row :=
  materialize_rows% (entry31.spec.targets C713Shared.dictionary)

private theorem base31_exact :
    base31 = entry31.spec.base C713Shared.dictionary := by decide +kernel
private theorem target31_exact :
    target31 = entry31.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric31 :
    PlanarVertexSparse.UnorderedCheck base31 [] target31 := by decide +kernel

theorem entry31_checked : entry31.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base31_exact, ← target31_exact] using numeric31
  · change entry31.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
