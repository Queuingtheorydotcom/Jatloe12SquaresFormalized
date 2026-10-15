import Completion.Cases.C981.VectorData
import Completion.Cases.C981.DiagonalAuxiliary

namespace S12Completion.C981
open S12 S12Pilot
/-- The exact inverse image on the original, sorted auxiliary tables. -/
def transposeAuxiliary (s : Finset Nat) : Finset Nat :=
  (Finset.univ.filter (fun j : Fin 20 => (auxiliaryTranspose j).val ∈ s)).image Fin.val

theorem transposeAuxiliary_mem (s : Finset Nat) (j : Fin 20) :
    j.val ∈ transposeAuxiliary s ↔ (auxiliaryTranspose j).val ∈ s := by
  simp only [transposeAuxiliary, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, he⟩
    have hkj : k = j := Fin.ext he
    simpa only [hkj] using hk
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem transposeAuxiliary_subset (s : Finset Nat) :
    transposeAuxiliary s ⊆ Finset.range 20 := by
  intro j hj
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr k.isLt

def transposeVector (v : List (Finset Nat)) : List (Finset Nat) :=
  List.ofFn (fun i : Fin 12 => transposeAuxiliary (v[(ownerTranspose i).val]!))


def coveredVectors : List (List (Finset Nat)) :=
  representativeVectors.flatMap (fun v => [v, transposeVector v])

end S12Completion.C981
