import Compact.Completion.OtherCases.C983.InitialDomains

/-! Sound local consistency refinement with literal field cuts between
stages. The original full auxiliary owner set survives every refinement. -/
namespace N12Compact.Completion.OtherCases.C983
open S12
open N12Compact.Completion.OtherCases.DomainTransport
set_option Elab.async false
noncomputable section

def stage1Owner0 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial0) 1
    [{2,12}] (by decide +kernel) (by decide +kernel)

def stage1Owner1 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial1) 2
    [{0,10}] (by decide +kernel) (by decide +kernel)

def stage1Owner2 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial2) 12
    [∅,{18},{6},{6,15},{6,18},{8,18},{6,8,18}] (by decide +kernel) (by decide +kernel)

def stage1Owner3 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial3) 48
    [∅,{19},{7},{7,17},{7,19},{9,19},{7,9,19}] (by decide +kernel) (by decide +kernel)

def stage1Owner4 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial4) 192
    [∅,{11},{1,11},{3},{3,11},{3,14},{1,3,11}] (by decide +kernel) (by decide +kernel)

def stage1Owner5 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial5) 512
    [{4,15},{4,16},{4,18},{4,15,16},{4,15,18},{4,16,18},{6,15},{6,16},{6,18},{6,15,16},{6,15,18},{6,16,18},{8,15},{8,16},{8,18},{8,15,16},{8,15,18},{8,16,18},{4,5,16},{4,5,15,16},{4,5,16,18},{4,6,15},{4,6,16},{4,6,18},{4,6,15,16},{4,6,15,18},{4,6,16,18},{4,8,15},{4,8,16},{4,8,18},{4,8,15,16},{4,8,15,18},{4,8,16,18},{4,9,16},{5,8,16},{5,8,15,16},{5,8,16,18},{6,8,15},{6,8,16},{6,8,18},{6,8,15,16},{6,8,15,18},{6,8,16,18},{4,5,6,16},{4,5,6,15,16},{4,5,6,16,18},{4,5,8,16},{4,5,8,15,16},{4,5,8,16,18},{4,5,9,16},{4,6,8,15},{4,6,8,16},{4,6,8,18},{4,6,8,15,16},{4,6,8,15,18},{4,6,8,16,18},{4,6,9,16},{5,6,8,16},{5,6,8,15,16},{5,6,8,16,18}] (by decide +kernel) (by decide +kernel)

def stage1Owner6 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial6) 1024
    [{5,16},{5,17},{5,19},{5,14,16},{5,16,17},{5,16,19},{5,17,19},{7,16},{7,17},{7,19},{7,16,17},{7,16,19},{7,17,19},{9,16},{9,17},{9,19},{9,16,17},{9,16,19},{9,17,19},{4,5,16},{4,5,14,16},{4,5,16,17},{4,5,16,19},{4,9,16},{4,9,16,17},{4,9,16,19},{5,7,16},{5,7,17},{5,7,19},{5,7,16,17},{5,7,16,19},{5,7,17,19},{5,8,16},{5,9,16},{5,9,17},{5,9,19},{5,9,16,17},{5,9,16,19},{5,9,17,19},{7,9,16},{7,9,17},{7,9,19},{7,9,16,17},{7,9,16,19},{7,9,17,19},{1,4,5,16},{1,4,5,14,16},{4,5,7,16},{4,5,7,16,17},{4,5,7,16,19},{4,5,8,16},{4,5,9,16},{4,5,9,16,17},{4,5,9,16,19},{4,7,9,16},{4,7,9,16,17},{4,7,9,16,19},{5,7,8,16},{5,7,9,16},{5,7,9,17},{5,7,9,19},{5,7,9,16,17},{5,7,9,16,19},{5,7,9,17,19}] (by decide +kernel) (by decide +kernel)

def stage1Owner7 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial7) 2304
    [{13},{11,13},{13,14},{13,16},{1,13},{1,11,13},{1,13,14},{1,13,16},{3,13},{3,11,13},{3,13,14},{4,13},{4,11,13},{4,13,14},{4,13,16},{5,13},{5,11,13},{5,13,14},{5,13,16},{1,3,13},{1,3,11,13},{1,3,13,14},{1,4,13},{1,4,11,13},{1,4,13,14},{1,4,13,16},{1,5,13},{1,5,11,13},{1,5,13,14},{1,5,13,16},{3,4,13},{3,4,11,13},{3,4,13,14},{3,5,13},{3,5,11,13},{3,5,13,14},{3,5,13,16},{4,5,13},{4,5,11,13},{4,5,13,14},{4,5,13,16}] (by decide +kernel) (by decide +kernel)

def stage1Owner8 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial8) 4096
    [{1,11},{1,3,11}] (by decide +kernel) (by decide +kernel)

def stage1Owner9 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial9) 8192
    [{6,15},{6,15,18},{4,6,15}] (by decide +kernel) (by decide +kernel)

def stage1Owner10 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial10) 16384
    [{8,18},{8,16,18},{9,19},{9,16,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19},{6,8,9,18},{7,8,9,19}] (by decide +kernel) (by decide +kernel)

def stage1Owner11 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial11) 32768
    [{3,14},{3,11,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17},{3,5,7,14,17}] (by decide +kernel) (by decide +kernel)

def stage1Named : List (NamedDomain family) :=
  [stage1Owner0,stage1Owner1,stage1Owner2,stage1Owner3,stage1Owner4,stage1Owner5,stage1Owner6,stage1Owner7,stage1Owner8,stage1Owner9,stage1Owner10,stage1Owner11]

end
end N12Compact.Completion.OtherCases.C983

