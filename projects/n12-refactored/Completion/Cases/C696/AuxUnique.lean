import Std.Tactic

/-!
C696 auxiliary bookkeeping, with no geometric assumptions hidden in the code.

The ten nonexempt owners are numbered here in the order
  [0,1,3,4,6,7,8,9,10,11].
For each family, `f i` is the index in that family's lexicographically sorted
ten-point list. Owners 2 and 5 are exempt and have the empty mask.

`FDomain` and `GDomain` are the independently reconstructed *single-family*
domains. Their geometric necessity is a separate premise; see aux-proof.md.
The theorem proves that disjoint strict ownership forces the unique assignment,
without coupled F/G domains, a search, native_decide, or additional axioms.
-/

namespace C696Aux

def Distinct10 (f : Nat → Nat) : Prop :=
  ∀ i, i < 10 → ∀ j, j < 10 → i ≠ j → f i ≠ f j

def FDomain (f : Nat → Nat) : Prop :=
  f 0 = 2 ∧ f 1 = 0 ∧ f 2 = 7 ∧ f 3 = 9 ∧
  (f 4 = 0 ∨ f 4 = 2 ∨ f 4 = 4) ∧
  (f 5 = 5 ∨ f 5 = 7 ∨ f 5 = 9) ∧
  (f 6 = 0 ∨ f 6 = 1) ∧
  (f 7 = 2 ∨ f 7 = 4 ∨ f 7 = 6) ∧
  (f 8 = 8 ∨ f 8 = 9) ∧
  (f 9 = 3 ∨ f 9 = 5 ∨ f 9 = 7)

def GDomain (g : Nat → Nat) : Prop :=
  g 0 = 2 ∧ g 1 = 0 ∧ g 2 = 7 ∧ g 3 = 9 ∧
  (g 4 = 0 ∨ g 4 = 2 ∨ g 4 = 3) ∧
  (g 5 = 6 ∨ g 5 = 7 ∨ g 5 = 9) ∧
  (g 6 = 0 ∨ g 6 = 1 ∨ g 6 = 3) ∧
  (g 7 = 2 ∨ g 7 = 5) ∧
  (g 8 = 6 ∨ g 8 = 8 ∨ g 8 = 9) ∧
  (g 9 = 4 ∨ g 9 = 7)

def FAssignment (f : Nat → Nat) : Prop :=
  f 0 = 2 ∧ f 1 = 0 ∧ f 2 = 7 ∧ f 3 = 9 ∧ f 4 = 4 ∧
  f 5 = 5 ∧ f 6 = 1 ∧ f 7 = 6 ∧ f 8 = 8 ∧ f 9 = 3

def GAssignment (g : Nat → Nat) : Prop :=
  g 0 = 2 ∧ g 1 = 0 ∧ g 2 = 7 ∧ g 3 = 9 ∧ g 4 = 3 ∧
  g 5 = 6 ∧ g 6 = 1 ∧ g 7 = 5 ∧ g 8 = 8 ∧ g 9 = 4

theorem f_unique (f : Nat → Nat) (hd : FDomain f) (hs : Distinct10 f) :
    FAssignment f := by
  rcases hd with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have n41 := hs 4 (by omega) 1 (by omega) (by omega)
  have n40 := hs 4 (by omega) 0 (by omega) (by omega)
  have n52 := hs 5 (by omega) 2 (by omega) (by omega)
  have n53 := hs 5 (by omega) 3 (by omega) (by omega)
  have n61 := hs 6 (by omega) 1 (by omega) (by omega)
  have n70 := hs 7 (by omega) 0 (by omega) (by omega)
  have n74 := hs 7 (by omega) 4 (by omega) (by omega)
  have n83 := hs 8 (by omega) 3 (by omega) (by omega)
  have n92 := hs 9 (by omega) 2 (by omega) (by omega)
  have n95 := hs 9 (by omega) 5 (by omega) (by omega)
  unfold FAssignment
  omega

theorem g_unique (g : Nat → Nat) (hd : GDomain g) (hs : Distinct10 g) :
    GAssignment g := by
  rcases hd with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have n41 := hs 4 (by omega) 1 (by omega) (by omega)
  have n40 := hs 4 (by omega) 0 (by omega) (by omega)
  have n52 := hs 5 (by omega) 2 (by omega) (by omega)
  have n53 := hs 5 (by omega) 3 (by omega) (by omega)
  have n61 := hs 6 (by omega) 1 (by omega) (by omega)
  have n64 := hs 6 (by omega) 4 (by omega) (by omega)
  have n70 := hs 7 (by omega) 0 (by omega) (by omega)
  have n83 := hs 8 (by omega) 3 (by omega) (by omega)
  have n85 := hs 8 (by omega) 5 (by omega) (by omega)
  have n92 := hs 9 (by omega) 2 (by omega) (by omega)
  unfold GAssignment
  omega

theorem unique_assignment (f g : Nat → Nat)
    (hf : FDomain f) (hg : GDomain g)
    (hdf : Distinct10 f) (hdg : Distinct10 g) :
    FAssignment f ∧ GAssignment g :=
  ⟨f_unique f hf hdf, g_unique g hg hdg⟩

#print axioms unique_assignment

end C696Aux
