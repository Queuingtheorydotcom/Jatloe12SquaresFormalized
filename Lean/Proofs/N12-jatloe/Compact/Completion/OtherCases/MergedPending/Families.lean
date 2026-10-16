import Compact.Completion.OtherCases.MergedPending.OriginalWalls

/-! Original entrances for C683, C700 and C867. The case selector only
selects the exact marker family; it asserts no symmetry between families.
The merged marker pairs remain in one actual owner throughout.
Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

inductive Case where
  | c683 | c700 | c867
  deriving DecidableEq

def family : Case→Finset Nat
  | .c683 => {1,2,12,16,32,192,256,512,3072,4096,8192,32768}
  | .c700 => {1,2,12,16,32,192,256,1536,4096,8192,16384,32768}
  | .c867 => {1,2,12,16,192,256,512,3072,4096,8192,16384,32768}

theorem common_member (k : Case) (m : Nat)
    (member : m∈({1,2,12,16,192,256,4096,8192,32768} : Finset Nat)) : m∈family k := by
  have subset : ({1,2,12,16,192,256,4096,8192,32768} : Finset Nat)⊆family k := by
    cases k <;> decide +kernel
  exact subset member

structure WallData (p : NormalizedPacking) : Prop where
  bottomSingleton : ∀ x : ℝ,28/25≤x → x≤87/50 → (owner p 1).Inside x 1
  leftSingleton : ∀ y : ℝ,28/25≤y → y≤87/50 → (owner p 2).Inside 1 y
  topSingleton : ∀ x : ℝ,113/50≤x → x≤72/25 → (owner p 16).Inside x 3
  leftCenter : 2<centerY (owner p 4096)
  leftChord : ∀ y : ℝ,111/50≤y → y≤239/100 → (owner p 4096).Inside 1 y
  bottomCenter : 2<centerX (owner p 8192)
  bottomChord : ∀ x : ℝ,111/50≤x → x≤239/100 → (owner p 8192).Inside x 1
  topCenter : centerX (owner p 32768)<2
  topChord : ∀ x : ℝ,161/100≤x → x≤89/50 → (owner p 32768).Inside x 3

theorem walls (k : Case) (p : NormalizedPacking) (hf : codedMarkerFamily p=family k) :
    WallData p := by
  have one := common_member k 1 (by decide)
  have two := common_member k 2 (by decide)
  have sixteen := common_member k 16 (by decide)
  have left := left_wall (family k) p hf (common_member k 4096 (by decide)) two
  have bottom := bottom_wall (family k) p hf (common_member k 8192 (by decide)) one
  have top := top_wall (family k) p hf (common_member k 32768 (by decide)) sixteen
  exact ⟨singleton_bottom _ p hf one,singleton_left _ p hf two,
    singleton_top _ p hf sixteen,left.1,left.2,bottom.1,bottom.2,top.1,top.2⟩

theorem c683_right_singleton (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c683) :
    ∀ y : ℝ,113/50≤y → y≤72/25 → (owner p 32).Inside 3 y :=
  singleton_right _ p hf (by decide +kernel)

theorem c700_right_singleton (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    ∀ y : ℝ,113/50≤y → y≤72/25 → (owner p 32).Inside 3 y :=
  singleton_right _ p hf (by decide +kernel)

theorem c700_right_wall (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    centerY (owner p 16384)<2 ∧
      ∀ y : ℝ,161/100≤y → y≤89/50 → (owner p 16384).Inside 3 y :=
  right_wall _ p hf (by decide +kernel) (by decide +kernel)

/-- Both upper markers are strictly inside the SAME merged3072. -/
theorem upper_merged_markers (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) :
    (owner p 3072).Inside (33/20) (47/20) ∧
      (owner p 3072).Inside (47/20) (47/20) := by
  have a := seed _ p hf 3072 member (33/20,47/20) (by decide +kernel)
  have b := seed _ p hf 3072 member (47/20,47/20) (by decide +kernel)
  norm_num at a b
  exact ⟨a,b⟩

/-- Both right markers are strictly inside the SAME merged1536. -/
theorem c700_merged_markers (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    (owner p 1536).Inside (47/20) (33/20) ∧
      (owner p 1536).Inside (47/20) (47/20) := by
  have a := seed _ p hf 1536 (by decide +kernel) (47/20,33/20) (by decide +kernel)
  have b := seed _ p hf 1536 (by decide +kernel) (47/20,47/20) (by decide +kernel)
  norm_num at a b
  exact ⟨a,b⟩

end
#print axioms walls
#print axioms c700_right_wall
end N12Compact.MergedPending
