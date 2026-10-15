import Compact.Completion.OtherCases.C715.InitialDomains

/-! Literal domain cuts after each sound refinement stage keep the kernel
checks finite and small. No actual label or F ownership allowance is dropped. -/

namespace N12Compact.Completion.OtherCases.C715
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
    [∅,{6}] (by decide +kernel) (by decide +kernel)

def stage1Owner3 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial3) 16
    [{7,17}] (by decide +kernel) (by decide +kernel)

def stage1Owner4 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial4) 32
    [{9,19}] (by decide +kernel) (by decide +kernel)

def stage1Owner5 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial5) 192
    [∅,{3}] (by decide +kernel) (by decide +kernel)

def stage1Owner6 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial6) 512
    [{4,15},{4,16},{4,18},{4,5,16},{6,15},{6,16},{6,18},{4,6,15},{4,6,16},{4,6,18},{8,15},{8,16},{8,18},{4,8,15},{4,8,16},{4,8,18},{5,8,16},{6,8,15},{6,8,16},{6,8,18}] (by decide +kernel) (by decide +kernel)

def stage1Owner7 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial7) 2304
    [{13},{1,13},{3,13},{4,13},{5,13}] (by decide +kernel) (by decide +kernel)

def stage1Owner8 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial8) 4096
    [{1,11},{1,3,11}] (by decide +kernel) (by decide +kernel)

def stage1Owner9 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial9) 8192
    [{6,15},{4,6,15}] (by decide +kernel) (by decide +kernel)

def stage1Owner10 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial10) 17408
    [{5,16},{5,18},{4,5,16},{4,5,18},{5,8,16},{5,8,18}] (by decide +kernel) (by decide +kernel)

def stage1Owner11 : NamedDomain family :=
  cacheNamed (initialNamed.foldl NamedDomain.refine initial11) 32768
    [{3,14},{3,5,14}] (by decide +kernel) (by decide +kernel)

def stage1Named : List (NamedDomain family) :=
  [stage1Owner0,stage1Owner1,stage1Owner2,stage1Owner3,stage1Owner4,stage1Owner5,stage1Owner6,stage1Owner7,stage1Owner8,stage1Owner9,stage1Owner10,stage1Owner11]

def stage2Owner0 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner0) 1
    [{2,12}] (by decide +kernel) (by decide +kernel)

def stage2Owner1 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner1) 2
    [{0,10}] (by decide +kernel) (by decide +kernel)

def stage2Owner2 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner2) 12
    [∅] (by decide +kernel) (by decide +kernel)

def stage2Owner3 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner3) 16
    [{7,17}] (by decide +kernel) (by decide +kernel)

def stage2Owner4 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner4) 32
    [{9,19}] (by decide +kernel) (by decide +kernel)

def stage2Owner5 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner5) 192
    [∅] (by decide +kernel) (by decide +kernel)

def stage2Owner6 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner6) 512
    [{4,16},{4,18},{8,16},{8,18},{4,8,16},{4,8,18}] (by decide +kernel) (by decide +kernel)

def stage2Owner7 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner7) 2304
    [{13},{4,13}] (by decide +kernel) (by decide +kernel)

def stage2Owner8 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner8) 4096
    [{1,11}] (by decide +kernel) (by decide +kernel)

def stage2Owner9 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner9) 8192
    [{6,15},{4,6,15}] (by decide +kernel) (by decide +kernel)

def stage2Owner10 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner10) 17408
    [{5,16},{5,18},{4,5,16},{4,5,18},{5,8,16},{5,8,18}] (by decide +kernel) (by decide +kernel)

def stage2Owner11 : NamedDomain family :=
  cacheNamed (stage1Named.foldl NamedDomain.refine stage1Owner11) 32768
    [{3,14}] (by decide +kernel) (by decide +kernel)

def stage2Named : List (NamedDomain family) :=
  [stage2Owner0,stage2Owner1,stage2Owner2,stage2Owner3,stage2Owner4,stage2Owner5,stage2Owner6,stage2Owner7,stage2Owner8,stage2Owner9,stage2Owner10,stage2Owner11]

def domains : List (CertifiedDomain family) := stage2Named.map NamedDomain.val

end
end N12Compact.Completion.OtherCases.C715
