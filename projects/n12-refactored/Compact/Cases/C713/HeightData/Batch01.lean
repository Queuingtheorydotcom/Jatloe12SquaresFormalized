import Compact.Cases.C713.HeightCore
import Compact.Core.RowMaterializeSyntax

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def entry8 : Entry :=
  ⟨⟨3196, ⟨0,10000000,-20564327,false⟩, some 3303⟩,
   ⟨(21743/16913),(3164327/10000000)⟩⟩

private def base8 : List Row :=
  materialize_rows% (entry8.spec.base C713Shared.dictionary)
private def target8 : List Row :=
  materialize_rows% (entry8.spec.targets C713Shared.dictionary)

private theorem base8_exact :
    base8 = entry8.spec.base C713Shared.dictionary := by decide +kernel
private theorem target8_exact :
    target8 = entry8.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric8 :
    PlanarVertexSparse.UnorderedCheck base8 [] target8 := by decide +kernel

theorem entry8_checked : entry8.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base8_exact, ← target8_exact] using numeric8
  · change entry8.TargetCheck
    decide +kernel

def entry9 : Entry :=
  ⟨⟨3197, ⟨0,25000000,-51237807,false⟩, some 3304⟩,
   ⟨(343/265),(7737807/25000000)⟩⟩

private def base9 : List Row :=
  materialize_rows% (entry9.spec.base C713Shared.dictionary)
private def target9 : List Row :=
  materialize_rows% (entry9.spec.targets C713Shared.dictionary)

private theorem base9_exact :
    base9 = entry9.spec.base C713Shared.dictionary := by decide +kernel
private theorem target9_exact :
    target9 = entry9.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric9 :
    PlanarVertexSparse.UnorderedCheck base9 [] target9 := by decide +kernel

theorem entry9_checked : entry9.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base9_exact, ← target9_exact] using numeric9
  · change entry9.TargetCheck
    decide +kernel

def entry10 : Entry :=
  ⟨⟨3198, ⟨0,50000000,-102138571,false⟩, some 3305⟩,
   ⟨(22159/17009),(15138571/50000000)⟩⟩

private def base10 : List Row :=
  materialize_rows% (entry10.spec.base C713Shared.dictionary)
private def target10 : List Row :=
  materialize_rows% (entry10.spec.targets C713Shared.dictionary)

private theorem base10_exact :
    base10 = entry10.spec.base C713Shared.dictionary := by decide +kernel
private theorem target10_exact :
    target10 = entry10.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric10 :
    PlanarVertexSparse.UnorderedCheck base10 [] target10 := by decide +kernel

theorem entry10_checked : entry10.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base10_exact, ← target10_exact] using numeric10
  · change entry10.TargetCheck
    decide +kernel

def entry11 : Entry :=
  ⟨⟨3199, ⟨0,1250000,-2545273,false⟩, some 3306⟩,
   ⟨(5591/4265),(370273/1250000)⟩⟩

private def base11 : List Row :=
  materialize_rows% (entry11.spec.base C713Shared.dictionary)
private def target11 : List Row :=
  materialize_rows% (entry11.spec.targets C713Shared.dictionary)

private theorem base11_exact :
    base11 = entry11.spec.base C713Shared.dictionary := by decide +kernel
private theorem target11_exact :
    target11 = entry11.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric11 :
    PlanarVertexSparse.UnorderedCheck base11 [] target11 := by decide +kernel

theorem entry11_checked : entry11.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base11_exact, ← target11_exact] using numeric11
  · change entry11.TargetCheck
    decide +kernel

def entry12 : Entry :=
  ⟨⟨3200, ⟨0,100000000,-202986099,false⟩, some 3307⟩,
   ⟨(22567/17113),(28986099/100000000)⟩⟩

private def base12 : List Row :=
  materialize_rows% (entry12.spec.base C713Shared.dictionary)
private def target12 : List Row :=
  materialize_rows% (entry12.spec.targets C713Shared.dictionary)

private theorem base12_exact :
    base12 = entry12.spec.base C713Shared.dictionary := by decide +kernel
private theorem target12_exact :
    target12 = entry12.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric12 :
    PlanarVertexSparse.UnorderedCheck base12 [] target12 := by decide +kernel

theorem entry12_checked : entry12.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base12_exact, ← target12_exact] using numeric12
  · change entry12.TargetCheck
    decide +kernel

def entry13 : Entry :=
  ⟨⟨3201, ⟨0,12500000,-25296331,false⟩, some 3308⟩,
   ⟨(1423/1073),(3546331/12500000)⟩⟩

private def base13 : List Row :=
  materialize_rows% (entry13.spec.base C713Shared.dictionary)
private def target13 : List Row :=
  materialize_rows% (entry13.spec.targets C713Shared.dictionary)

private theorem base13_exact :
    base13 = entry13.spec.base C713Shared.dictionary := by decide +kernel
private theorem target13_exact :
    target13 = entry13.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric13 :
    PlanarVertexSparse.UnorderedCheck base13 [] target13 := by decide +kernel

theorem entry13_checked : entry13.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base13_exact, ← target13_exact] using numeric13
  · change entry13.TargetCheck
    decide +kernel

def entry14 : Entry :=
  ⟨⟨3202, ⟨0,20000000,-40355233,false⟩, some 3309⟩,
   ⟨(22967/17225),(5555233/20000000)⟩⟩

private def base14 : List Row :=
  materialize_rows% (entry14.spec.base C713Shared.dictionary)
private def target14 : List Row :=
  materialize_rows% (entry14.spec.targets C713Shared.dictionary)

private theorem base14_exact :
    base14 = entry14.spec.base C713Shared.dictionary := by decide +kernel
private theorem target14_exact :
    target14 = entry14.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric14 :
    PlanarVertexSparse.UnorderedCheck base14 [] target14 := by decide +kernel

theorem entry14_checked : entry14.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base14_exact, ← target14_exact] using numeric14
  · change entry14.TargetCheck
    decide +kernel

def entry15 : Entry :=
  ⟨⟨3203, ⟨0,100000000,-201203279,false⟩, some 3310⟩,
   ⟨(5791/4321),(27203279/100000000)⟩⟩

private def base15 : List Row :=
  materialize_rows% (entry15.spec.base C713Shared.dictionary)
private def target15 : List Row :=
  materialize_rows% (entry15.spec.targets C713Shared.dictionary)

private theorem base15_exact :
    base15 = entry15.spec.base C713Shared.dictionary := by decide +kernel
private theorem target15_exact :
    target15 = entry15.spec.targets C713Shared.dictionary := by decide +kernel
private theorem numeric15 :
    PlanarVertexSparse.UnorderedCheck base15 [] target15 := by decide +kernel

theorem entry15_checked : entry15.Check := by
  refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
  · simpa only [← base15_exact, ← target15_exact] using numeric15
  · change entry15.TargetCheck
    decide +kernel


end N12Compact.C713HeightData
