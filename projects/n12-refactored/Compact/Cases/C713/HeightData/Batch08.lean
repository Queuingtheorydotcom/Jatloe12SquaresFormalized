import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry64 : Entry :=
  ⟨⟨3252, ⟨0,100000000,-201035981,false⟩, some 3359⟩,
   ⟨(30367/22625),(27035981/100000000)⟩⟩

private def base64 : List Row :=
  materialize_rows% (entry64.spec.base C713Shared.dictionary)
private def target64 : List Row :=
  materialize_rows% (entry64.spec.targets C713Shared.dictionary)

private theorem base64_exact :
    base64 = entry64.spec.base C713Shared.dictionary := by decide +kernel
private theorem target64_exact :
    target64 = entry64.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric64 :
    PlanarVertexSparse.UnorderedCheck base64 [] target64 := by decide +kernel

theorem entry64_checked : entry64.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base64_exact, ← target64_exact] using numeric64
  · change entry64.TargetCheck
    decide +kernel

def entry65 : Entry :=
  ⟨⟨3253, ⟨0,50000000,-100732483,false⟩, some 3360⟩,
   ⟨(119/89),(13732483/50000000)⟩⟩

private def base65 : List Row :=
  materialize_rows% (entry65.spec.base C713Shared.dictionary)
private def target65 : List Row :=
  materialize_rows% (entry65.spec.targets C713Shared.dictionary)

private theorem base65_exact :
    base65 = entry65.spec.base C713Shared.dictionary := by decide +kernel
private theorem target65_exact :
    target65 = entry65.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric65 :
    PlanarVertexSparse.UnorderedCheck base65 [] target65 := by decide +kernel

theorem entry65_checked : entry65.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base65_exact, ← target65_exact] using numeric65
  · change entry65.TargetCheck
    decide +kernel

def entry66 : Entry :=
  ⟨⟨3254, ⟨0,2500000,-5047559,false⟩, some 3361⟩,
   ⟨(30559/22945),(697559/2500000)⟩⟩

private def base66 : List Row :=
  materialize_rows% (entry66.spec.base C713Shared.dictionary)
private def target66 : List Row :=
  materialize_rows% (entry66.spec.targets C713Shared.dictionary)

private theorem base66_exact :
    base66 = entry66.spec.base C713Shared.dictionary := by decide +kernel
private theorem target66_exact :
    target66 = entry66.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric66 :
    PlanarVertexSparse.UnorderedCheck base66 [] target66 := by decide +kernel

theorem entry66_checked : entry66.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base66_exact, ← target66_exact] using numeric66
  · change entry66.TargetCheck
    decide +kernel

def entry67 : Entry :=
  ⟨⟨3255, ⟨0,25000000,-50586903,false⟩, some 3362⟩,
   ⟨(7663/5777),(7086903/25000000)⟩⟩

private def base67 : List Row :=
  materialize_rows% (entry67.spec.base C713Shared.dictionary)
private def target67 : List Row :=
  materialize_rows% (entry67.spec.targets C713Shared.dictionary)

private theorem base67_exact :
    base67 = entry67.spec.base C713Shared.dictionary := by decide +kernel
private theorem target67_exact :
    target67 = entry67.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric67 :
    PlanarVertexSparse.UnorderedCheck base67 [] target67 := by decide +kernel

theorem entry67_checked : entry67.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base67_exact, ← target67_exact] using numeric67
  · change entry67.TargetCheck
    decide +kernel

def entry68 : Entry :=
  ⟨⟨3256, ⟨0,50000000,-101400091,false⟩, some 3363⟩,
   ⟨(30743/23273),(14400091/50000000)⟩⟩

private def base68 : List Row :=
  materialize_rows% (entry68.spec.base C713Shared.dictionary)
private def target68 : List Row :=
  materialize_rows% (entry68.spec.targets C713Shared.dictionary)

private theorem base68_exact :
    base68 = entry68.spec.base C713Shared.dictionary := by decide +kernel
private theorem target68_exact :
    target68 = entry68.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric68 :
    PlanarVertexSparse.UnorderedCheck base68 [] target68 := by decide +kernel

theorem entry68_checked : entry68.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base68_exact, ← target68_exact] using numeric68
  · change entry68.TargetCheck
    decide +kernel

def entry69 : Entry :=
  ⟨⟨3257, ⟨0,100000000,-203259537,false⟩, some 3364⟩,
   ⟨(1927/1465),(29259537/100000000)⟩⟩

private def base69 : List Row :=
  materialize_rows% (entry69.spec.base C713Shared.dictionary)
private def target69 : List Row :=
  materialize_rows% (entry69.spec.targets C713Shared.dictionary)

private theorem base69_exact :
    base69 = entry69.spec.base C713Shared.dictionary := by decide +kernel
private theorem target69_exact :
    target69 = entry69.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric69 :
    PlanarVertexSparse.UnorderedCheck base69 [] target69 := by decide +kernel

theorem entry69_checked : entry69.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base69_exact, ← target69_exact] using numeric69
  · change entry69.TargetCheck
    decide +kernel

def entry70 : Entry :=
  ⟨⟨3258, ⟨0,2000000,-4074503,false⟩, some 3365⟩,
   ⟨(30919/23609),(594503/2000000)⟩⟩

private def base70 : List Row :=
  materialize_rows% (entry70.spec.base C713Shared.dictionary)
private def target70 : List Row :=
  materialize_rows% (entry70.spec.targets C713Shared.dictionary)

private theorem base70_exact :
    base70 = entry70.spec.base C713Shared.dictionary := by decide +kernel
private theorem target70_exact :
    target70 = entry70.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric70 :
    PlanarVertexSparse.UnorderedCheck base70 [] target70 := by decide +kernel

theorem entry70_checked : entry70.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base70_exact, ← target70_exact] using numeric70
  · change entry70.TargetCheck
    decide +kernel

def entry71 : Entry :=
  ⟨⟨3259, ⟨0,25000000,-51049127,false⟩, some 3366⟩,
   ⟨(7751/5945),(7549127/25000000)⟩⟩

private def base71 : List Row :=
  materialize_rows% (entry71.spec.base C713Shared.dictionary)
private def target71 : List Row :=
  materialize_rows% (entry71.spec.targets C713Shared.dictionary)

private theorem base71_exact :
    base71 = entry71.spec.base C713Shared.dictionary := by decide +kernel
private theorem target71_exact :
    target71 = entry71.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric71 :
    PlanarVertexSparse.UnorderedCheck base71 [] target71 := by decide +kernel

theorem entry71_checked : entry71.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base71_exact, ← target71_exact] using numeric71
  · change entry71.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
