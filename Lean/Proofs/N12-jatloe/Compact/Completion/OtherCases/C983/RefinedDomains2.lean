import Compact.Completion.OtherCases.C983.RefinedDomains1

/-! Sound local consistency refinement with literal field cuts between
stages. The original full auxiliary owner set survives every refinement. -/
namespace N12Compact.Completion.OtherCases.C983
open S12
open N12Compact.Completion.OtherCases.DomainTransport
set_option Elab.async false
noncomputable section

def stage2Owner0 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner0) 1
    [{2,12}] (by decide +kernel) (by decide +kernel)

def stage2Owner1 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner1) 2
    [{0,10}] (by decide +kernel) (by decide +kernel)

def stage2Owner2 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner2) 12
    [∅,{18},{8,18}] (by decide +kernel) (by decide +kernel)

def stage2Owner3 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner3) 48
    [∅,{19},{7},{7,17},{7,19},{9,19},{7,9,19}] (by decide +kernel) (by decide +kernel)

def stage2Owner4 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner4) 192
    [∅,{3},{3,14}] (by decide +kernel) (by decide +kernel)

def stage2Owner5 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner5) 512
    [{4,16},{4,18},{4,16,18},{8,16},{8,18},{8,16,18},{4,5,16},{4,5,16,18},{4,8,16},{4,8,18},{4,8,16,18},{4,9,16},{5,8,16},{5,8,16,18},{4,5,8,16},{4,5,8,16,18},{4,5,9,16}] (by decide +kernel) (by decide +kernel)

def stage2Owner6 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner6) 1024
    [{5,16},{5,17},{5,19},{5,14,16},{5,16,17},{5,16,19},{5,17,19},{7,16},{7,17},{7,19},{7,16,17},{7,16,19},{7,17,19},{9,16},{9,17},{9,19},{9,16,17},{9,16,19},{9,17,19},{4,5,16},{4,5,14,16},{4,5,16,17},{4,5,16,19},{4,9,16},{4,9,16,17},{4,9,16,19},{5,7,16},{5,7,17},{5,7,19},{5,7,16,17},{5,7,16,19},{5,7,17,19},{5,8,16},{5,9,16},{5,9,17},{5,9,19},{5,9,16,17},{5,9,16,19},{5,9,17,19},{7,9,16},{7,9,17},{7,9,19},{7,9,16,17},{7,9,16,19},{7,9,17,19},{4,5,7,16},{4,5,7,16,17},{4,5,7,16,19},{4,5,8,16},{4,5,9,16},{4,5,9,16,17},{4,5,9,16,19},{4,7,9,16},{4,7,9,16,17},{4,7,9,16,19},{5,7,8,16},{5,7,9,16},{5,7,9,17},{5,7,9,19},{5,7,9,16,17},{5,7,9,16,19},{5,7,9,17,19}] (by decide +kernel) (by decide +kernel)

def stage2Owner7 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner7) 2304
    [{13},{13,14},{13,16},{3,13},{3,13,14},{4,13},{4,13,14},{4,13,16},{5,13},{5,13,14},{5,13,16},{3,4,13},{3,4,13,14},{3,5,13},{3,5,13,14},{3,5,13,16},{4,5,13},{4,5,13,14},{4,5,13,16}] (by decide +kernel) (by decide +kernel)

def stage2Owner8 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner8) 4096
    [{1,11},{1,3,11}] (by decide +kernel) (by decide +kernel)

def stage2Owner9 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner9) 8192
    [{6,15},{6,15,18},{4,6,15}] (by decide +kernel) (by decide +kernel)

def stage2Owner10 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner10) 16384
    [{8,18},{8,16,18},{9,19},{9,16,19},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19},{7,8,9,19}] (by decide +kernel) (by decide +kernel)

def stage2Owner11 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner11) 32768
    [{3,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17},{3,5,7,14,17}] (by decide +kernel) (by decide +kernel)

def stage2Named : List (NamedDomain family) :=
  [stage2Owner0,stage2Owner1,stage2Owner2,stage2Owner3,stage2Owner4,stage2Owner5,stage2Owner6,stage2Owner7,stage2Owner8,stage2Owner9,stage2Owner10,stage2Owner11]

end
end N12Compact.Completion.OtherCases.C983

