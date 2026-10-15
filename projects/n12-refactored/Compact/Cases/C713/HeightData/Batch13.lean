import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry104 : Entry :=
  ⟨⟨3292, ⟨0,25000000,-55597377,false⟩, none⟩,
   ⟨(2047/1985),(12097377/25000000)⟩⟩

private def base104 : List Row :=
  materialize_rows% (entry104.spec.base C713Shared.dictionary)
private def target104 : List Row :=
  materialize_rows% (entry104.spec.targets C713Shared.dictionary)

private theorem base104_exact :
    base104 = entry104.spec.base C713Shared.dictionary := by decide +kernel
private theorem target104_exact :
    target104 = entry104.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric104 :
    PlanarVertexSparse.UnorderedCheck base104 [] target104 := by decide +kernel

theorem entry104_checked : entry104.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base104_exact, ← target104_exact] using numeric104
  · change entry104.TargetCheck
    decide +kernel

def entry105 : Entry :=
  ⟨⟨3293, ⟨0,25000000,-55700251,false⟩, none⟩,
   ⟨(32759/32009),(12200251/25000000)⟩⟩

private def base105 : List Row :=
  materialize_rows% (entry105.spec.base C713Shared.dictionary)
private def target105 : List Row :=
  materialize_rows% (entry105.spec.targets C713Shared.dictionary)

private theorem base105_exact :
    base105 = entry105.spec.base C713Shared.dictionary := by decide +kernel
private theorem target105_exact :
    target105 = entry105.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric105 :
    PlanarVertexSparse.UnorderedCheck base105 [] target105 := by decide +kernel

theorem entry105_checked : entry105.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base105_exact, ← target105_exact] using numeric105
  · change entry105.TargetCheck
    decide +kernel

def entry106 : Entry :=
  ⟨⟨3294, ⟨0,50000000,-111603321,false⟩, none⟩,
   ⟨(8191/8065),(24603321/50000000)⟩⟩

private def base106 : List Row :=
  materialize_rows% (entry106.spec.base C713Shared.dictionary)
private def target106 : List Row :=
  materialize_rows% (entry106.spec.targets C713Shared.dictionary)

private theorem base106_exact :
    base106 = entry106.spec.base C713Shared.dictionary := by decide +kernel
private theorem target106_exact :
    target106 = entry106.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric106 :
    PlanarVertexSparse.UnorderedCheck base106 [] target106 := by decide +kernel

theorem entry106_checked : entry106.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base106_exact, ← target106_exact] using numeric106
  · change entry106.TargetCheck
    decide +kernel

def entry107 : Entry :=
  ⟨⟨3295, ⟨0,20000000,-44721267,false⟩, none⟩,
   ⟨(32767/32513),(9921267/20000000)⟩⟩

private def base107 : List Row :=
  materialize_rows% (entry107.spec.base C713Shared.dictionary)
private def target107 : List Row :=
  materialize_rows% (entry107.spec.targets C713Shared.dictionary)

private theorem base107_exact :
    base107 = entry107.spec.base C713Shared.dictionary := by decide +kernel
private theorem target107_exact :
    target107 = entry107.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric107 :
    PlanarVertexSparse.UnorderedCheck base107 [] target107 := by decide +kernel

theorem entry107_checked : entry107.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base107_exact, ← target107_exact] using numeric107
  · change entry107.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
