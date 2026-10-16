import Compact.Completion.CommonCases.OriginalOwners

/-! C1091's literal original owners. All square indices below refer to
the displayed ascending mask list. In particular Q4 owns markers1 and8;
the marker1 omission is specific to Q0, never global. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

def family : Finset Nat := {1,12,48,192,258,512,1024,2048,4096,8192,16384,32768}
def masks : Fin 12 → Nat := ![1,12,48,192,258,512,1024,2048,4096,8192,16384,32768]
def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  CommonCases.OriginalOwners.owner p (masks i)

theorem member (i : Fin 12) : masks i∈family := by
  have all : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact all i

private theorem injective : Function.Injective masks := by decide +kernel

theorem side (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side :=
  CommonCases.OriginalOwners.side p (masks i)
theorem cap (p : NormalizedPacking) (i : Fin 12) : (owners p i).side≤1001/1000 := by
  change (p.square (ownerIndex p (masks i))).side≤1001/1000
  rw [p.congruent]
  exact p.side_le
theorem same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm
theorem box (p : NormalizedPacking) (i : Fin 12) : InsideContainer (owners p i) :=
  CommonCases.OriginalOwners.box p (masks i)
theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
  CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
    (member i) (member j) (fun equal => different (injective equal))
theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport (masks i))) :
    (owners p i).Inside P.1 P.2 :=
  CommonCases.OriginalOwners.seed family p hf (masks i) (member i) P checked

theorem auxiliary (p : NormalizedPacking) (i : Fin 12) (j : Nat) (bound : j<20) :
    (owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 ↔
      j∈CommonCases.OriginalOwners.auxiliaries p (masks i) :=
  CommonCases.OriginalOwners.auxiliary_exact p (masks i) j bound

theorem merged_markers (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 4).Inside (457/500) 1 ∧ (owners p 4).Inside (33/20) (33/20) := by
  have left := seed p hf 4 (457/500,1) (by decide +kernel)
  have central := seed p hf 4 (33/20,33/20) (by decide +kernel)
  norm_num at left central
  exact ⟨left,central⟩

theorem singleton_missing_marker1 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : ¬(owners p 0).Inside (457/500) 1 := by
  have result := CommonCases.OriginalOwners.missing_marker family p hf (masks 0)
    (member 0) 1 (by decide +kernel)
  simpa [owners,marker] using result

end
#print axioms merged_markers
end N12Compact.Completion.OtherCases.C1091.OriginalData
