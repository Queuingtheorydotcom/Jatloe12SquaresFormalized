import Compact.Cases.C898.CachedPairs.Step04RawData
import Compact.Core.CommonPoint
import Compact.Core.KernelMatrix

/-! Seven common points cover 434 original pairs; fourteen remaining pairs
retain their original eight-axis checks. Every original source and neighbor
is covered, without convex combinations or a sampled containment claim. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared
noncomputable section

def step4CommonPoints : Fin 7 → CommonPoint.Point := ![
  ⟨2966, 1977, 1000⟩,
  ⟨2941, 1973, 1000⟩,
  ⟨3074, 2012, 1000⟩,
  ⟨3173, 2045, 1000⟩,
  ⟨3111, 2023, 1000⟩,
  ⟨3048, 2000, 1000⟩,
  ⟨3021, 1991, 1000⟩]

def step4OwnKeys (angle : Fin 64) (i : Fin 4) : Nat :=
  fanDirectionKey angle angle ⟨i.val, by omega⟩

/-- Input index zero denotes original neighbor two. -/
def step4GeometricNeighbor (j : Fin 62) : Fin 64 := ⟨j.val + 2, by omega⟩

def step4PointGroup (j : Fin 62) : Fin 7 :=
  if j.val < 2 then 0 else
  if j.val < 6 then 1 else
  if j.val < 14 then 2 else
  if j.val < 30 then 3 else
  if j.val < 46 then 4 else
  if j.val < 54 then 5 else 6

kernel_matrix step4_source_points_checked : 7 × 7 => (fun i g =>
  CommonPoint.check (step4RawSources i) (step4OwnKeys (step4RawSourceAngle i))
    (step4CommonPoints g) = true)

kernel_matrix step4_neighbor_points_checked : 62 × 1 => (fun j _ =>
  CommonPoint.check (step4RawNeighbors (step4GeometricNeighbor j))
    (step4OwnKeys (step4GeometricNeighbor j))
    (step4CommonPoints (step4PointGroup j)) = true)

kernel_matrix step4_fallback_pairs_checked : 7 × 2 => (fun i j =>
  step4RawPairCheck i ⟨j.val, by omega⟩)

#print axioms step4_source_points_checked
#print axioms step4_neighbor_points_checked
#print axioms step4_fallback_pairs_checked

end
end N12Compact.C898Cached.AllPairs
