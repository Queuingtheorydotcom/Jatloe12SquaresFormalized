import Compact.Bridge.FourSquareVectorCover

/-! Four geometric patterns suffice for every merged-lower family.
There are twelve exact owner-set bindings of these patterns. Reflections are
performed on the original packing, not on a saved polygon or sampled angle. -/
namespace N12Compact.MergedLower
open S12 FourSquareVectorCover
set_option Elab.async false

def upperNE (a b l r : Finset Nat) : Recipe :=
  .inl ⟨⟨false,false,false⟩,![1024,2048,4096,16384],![a,b,l,r],2,8⟩

def upperNW (a b l r : Finset Nat) : Recipe :=
  .inl ⟨⟨false,true,false⟩,![2048,1024,16384,4096],![b,a,r,l],8,2⟩

def spanNE (a b l r : Finset Nat) : Recipe :=
  .inr ⟨⟨false,false,false⟩,![1024,2048,4096,16384],![a,b,l,r],8/5⟩

def spanNW (a b l r : Finset Nat) : Recipe :=
  .inr ⟨⟨false,true,false⟩,![2048,1024,16384,4096],![b,a,r,l],8/5⟩

def recipes : List Recipe :=
  [upperNE {5,13,16} {3,14} {1,11} {9,19},
   upperNE {5,16} {3,13,14} {1,11} {9,19},
   upperNE {5,16} {3,14} {1,11} {9,19},
   upperNE {5,16} {3,14} {1,11,13} {9,19},
   upperNW {7,16,17} {5,13} {1,11} {9,19},
   upperNW {7,17} {5,13} {1,11} {9,16,19},
   upperNW {7,17} {5,13} {1,11} {9,19},
   upperNW {7,17} {5,13,16} {1,11} {9,19},
   spanNE {5,14,16} {3,13} {1,11} {9,19},
   spanNE {5,16} {3,13} {1,11} {9,19},
   spanNW {7,16} {5,13} {1,11} {9,19},
   spanNW {7,16} {5,13,17} {1,11} {9,19}]

end N12Compact.MergedLower
