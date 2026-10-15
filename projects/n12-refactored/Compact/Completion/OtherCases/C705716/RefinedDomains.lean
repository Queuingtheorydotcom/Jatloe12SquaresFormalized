import Compact.Completion.OtherCases.C705716.InitialDomains

/-! Cached exact owner-label refinements. Each stage uses complete sound
incoming domains and records a checked literal output before the next stage. -/

namespace N12Compact.Completion.OtherCases.C705716
open S12
open N12Compact.Completion.OtherCases.DomainTransport
set_option Elab.async false
noncomputable section

def stage1Owner0 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial0 b)) 1
    [{2,12}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner1 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial1 b)) 2
    [{0,10}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner2 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial2 b)) 12
    [∅,{18},{6},{6,15},{6,18},{8,18}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner3 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial3 b)) 16
    [{7,17}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner4 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial4 b)) 32
    [{9,19}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner5 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial5 b)) 192
    [∅,{11},{1,11},{3},{3,11},{3,14}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner6 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial6 b)) (if b then 512 else 256)
    (if b then [{4,15},{4,16},{4,15,16},{4,18},{4,15,18},{4,16,18},{6,15},{6,16},{6,15,16},{6,18},{6,15,18},{6,16,18},{4,6,15},{4,6,16},{4,6,15,16},{4,6,18},{4,6,15,18},{4,6,16,18},{8,15},{8,16},{8,15,16},{8,18},{8,15,18},{8,16,18},{4,8,15},{4,8,16},{4,8,15,16},{4,8,18},{4,8,15,18},{4,8,16,18},{6,8,15},{6,8,16},{6,8,15,16},{6,8,18},{6,8,15,18},{6,8,16,18}] else [{4,13},{4,13,15},{1,4,13},{1,4,13,15}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner7 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial7 b)) (if b then 3328 else 3584)
    (if b then [{5,13}] else [{5,16}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner8 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial8 b)) 4096
    (if b then [{1,11},{1,3,11}] else [{1,11},{1,11,13},{1,3,11}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner9 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial9 b)) 8192
    [{6,15},{6,15,18},{4,6,15}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner10 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial10 b)) 16384
    (if b then [{8,18},{8,16,18},{6,8,18}] else [{8,18},{6,8,18}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Owner11 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((initialNamed b).foldl NamedDomain.refine (initial11 b)) 32768
    [{3,14},{3,11,14}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage1Named (b : Bool) : List (NamedDomain (family b)) :=
  [stage1Owner0 b,stage1Owner1 b,stage1Owner2 b,stage1Owner3 b,stage1Owner4 b,stage1Owner5 b,stage1Owner6 b,stage1Owner7 b,stage1Owner8 b,stage1Owner9 b,stage1Owner10 b,stage1Owner11 b]

def stage2Owner0 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner0 b)) 1
    [{2,12}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner1 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner1 b)) 2
    [{0,10}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner2 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner2 b)) 12
    [∅] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner3 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner3 b)) 16
    [{7,17}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner4 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner4 b)) 32
    [{9,19}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner5 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner5 b)) 192
    [∅] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner6 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner6 b)) (if b then 512 else 256)
    (if b then [{4,16}] else [{4,13}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner7 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner7 b)) (if b then 3328 else 3584)
    (if b then [{5,13}] else [{5,16}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner8 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner8 b)) 4096
    [{1,11}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner9 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner9 b)) 8192
    (if b then [{6,15},{4,6,15}] else [{6,15}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner10 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner10 b)) 16384
    (if b then [{8,18},{8,16,18}] else [{8,18}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Owner11 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage1Named b).foldl NamedDomain.refine (stage1Owner11 b)) 32768
    [{3,14}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage2Named (b : Bool) : List (NamedDomain (family b)) :=
  [stage2Owner0 b,stage2Owner1 b,stage2Owner2 b,stage2Owner3 b,stage2Owner4 b,stage2Owner5 b,stage2Owner6 b,stage2Owner7 b,stage2Owner8 b,stage2Owner9 b,stage2Owner10 b,stage2Owner11 b]

def stage3Owner0 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner0 b)) 1
    [{2,12}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner1 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner1 b)) 2
    [{0,10}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner2 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner2 b)) 12
    [∅] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner3 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner3 b)) 16
    [{7,17}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner4 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner4 b)) 32
    [{9,19}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner5 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner5 b)) 192
    [∅] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner6 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner6 b)) (if b then 512 else 256)
    (if b then [{4,16}] else [{4,13}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner7 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner7 b)) (if b then 3328 else 3584)
    (if b then [{5,13}] else [{5,16}]) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner8 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner8 b)) 4096
    [{1,11}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner9 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner9 b)) 8192
    [{6,15}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner10 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner10 b)) 16384
    [{8,18}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Owner11 (b : Bool) : NamedDomain (family b) :=
  cacheNamed ((stage2Named b).foldl NamedDomain.refine (stage2Owner11 b)) 32768
    [{3,14}] (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

def stage3Named (b : Bool) : List (NamedDomain (family b)) :=
  [stage3Owner0 b,stage3Owner1 b,stage3Owner2 b,stage3Owner3 b,stage3Owner4 b,stage3Owner5 b,stage3Owner6 b,stage3Owner7 b,stage3Owner8 b,stage3Owner9 b,stage3Owner10 b,stage3Owner11 b]

def domains (b : Bool) : List (CertifiedDomain (family b)) :=
  (stage3Named b).map NamedDomain.val

end
end N12Compact.Completion.OtherCases.C705716
