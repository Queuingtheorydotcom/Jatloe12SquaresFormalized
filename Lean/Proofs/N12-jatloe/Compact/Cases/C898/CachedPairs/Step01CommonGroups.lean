import Compact.Cases.C898.CachedPairs.Step01CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step1CommonScope0 : Scope := ⟨0, 64, 0, 1⟩
theorem step1CommonScope0_valid : step1CommonScope0.Valid 64 64 := by decide +kernel

kernel_matrix step1CommonGroup0_checked : 64 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step1CommonRawSources (step1CommonScope0.sourceIndex step1CommonScope0_valid a))
    (step1CommonRawNeighbors (step1CommonScope0.neighborIndex step1CommonScope0_valid b))
    (fanDirectionKey (step1CommonSourceAngles (step1CommonScope0.sourceIndex step1CommonScope0_valid a))
      (step1CommonNeighborAngles (step1CommonScope0.neighborIndex step1CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step1CommonGroup0 : CheckedGroup step1Sources step1Neighbors := fallbackGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope0 step1CommonScope0_valid
  step1CommonSourceAngles step1CommonNeighborAngles
  step1CommonSourceAngles_exact step1CommonNeighborAngles_exact
  step1CommonGroup0_checked

def step1CommonScope1 : Scope := ⟨0, 64, 1, 1⟩
theorem step1CommonScope1_valid : step1CommonScope1.Valid 64 64 := by decide +kernel

def step1CommonPoint1 : CommonPoint.Point := ⟨3073, 1347, 1000⟩
kernel_matrix step1CommonGroup1_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope1.sourceIndex step1CommonScope1_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope1.sourceIndex step1CommonScope1_valid a))) step1CommonPoint1 = true)
kernel_matrix step1CommonGroup1_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope1.neighborIndex step1CommonScope1_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope1.neighborIndex step1CommonScope1_valid b))) step1CommonPoint1 = true)
def step1CommonGroup1 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope1 step1CommonScope1_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint1
  (fun a => step1CommonGroup1_sources a 0) (fun b => step1CommonGroup1_neighbors b 0)

def step1CommonScope2 : Scope := ⟨0, 64, 2, 2⟩
theorem step1CommonScope2_valid : step1CommonScope2.Valid 64 64 := by decide +kernel

def step1CommonPoint2 : CommonPoint.Point := ⟨769, 335, 250⟩
kernel_matrix step1CommonGroup2_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope2.sourceIndex step1CommonScope2_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope2.sourceIndex step1CommonScope2_valid a))) step1CommonPoint2 = true)
kernel_matrix step1CommonGroup2_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope2.neighborIndex step1CommonScope2_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope2.neighborIndex step1CommonScope2_valid b))) step1CommonPoint2 = true)
def step1CommonGroup2 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope2 step1CommonScope2_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint2
  (fun a => step1CommonGroup2_sources a 0) (fun b => step1CommonGroup2_neighbors b 0)

def step1CommonScope3 : Scope := ⟨0, 64, 4, 4⟩
theorem step1CommonScope3_valid : step1CommonScope3.Valid 64 64 := by decide +kernel

def step1CommonPoint3 : CommonPoint.Point := ⟨3085, 1341, 1000⟩
kernel_matrix step1CommonGroup3_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope3.sourceIndex step1CommonScope3_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope3.sourceIndex step1CommonScope3_valid a))) step1CommonPoint3 = true)
kernel_matrix step1CommonGroup3_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope3.neighborIndex step1CommonScope3_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope3.neighborIndex step1CommonScope3_valid b))) step1CommonPoint3 = true)
def step1CommonGroup3 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope3 step1CommonScope3_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint3
  (fun a => step1CommonGroup3_sources a 0) (fun b => step1CommonGroup3_neighbors b 0)

def step1CommonScope4 : Scope := ⟨0, 64, 8, 8⟩
theorem step1CommonScope4_valid : step1CommonScope4.Valid 64 64 := by decide +kernel

def step1CommonPoint4 : CommonPoint.Point := ⟨3094, 1349, 1000⟩
kernel_matrix step1CommonGroup4_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope4.sourceIndex step1CommonScope4_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope4.sourceIndex step1CommonScope4_valid a))) step1CommonPoint4 = true)
kernel_matrix step1CommonGroup4_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope4.neighborIndex step1CommonScope4_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope4.neighborIndex step1CommonScope4_valid b))) step1CommonPoint4 = true)
def step1CommonGroup4 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope4 step1CommonScope4_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint4
  (fun a => step1CommonGroup4_sources a 0) (fun b => step1CommonGroup4_neighbors b 0)

def step1CommonScope5 : Scope := ⟨0, 64, 16, 16⟩
theorem step1CommonScope5_valid : step1CommonScope5.Valid 64 64 := by decide +kernel

def step1CommonPoint5 : CommonPoint.Point := ⟨3115, 1381, 1000⟩
kernel_matrix step1CommonGroup5_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope5.sourceIndex step1CommonScope5_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope5.sourceIndex step1CommonScope5_valid a))) step1CommonPoint5 = true)
kernel_matrix step1CommonGroup5_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope5.neighborIndex step1CommonScope5_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope5.neighborIndex step1CommonScope5_valid b))) step1CommonPoint5 = true)
def step1CommonGroup5 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope5 step1CommonScope5_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint5
  (fun a => step1CommonGroup5_sources a 0) (fun b => step1CommonGroup5_neighbors b 0)

def step1CommonScope6 : Scope := ⟨0, 64, 32, 16⟩
theorem step1CommonScope6_valid : step1CommonScope6.Valid 64 64 := by decide +kernel

def step1CommonPoint6 : CommonPoint.Point := ⟨623, 276, 200⟩
kernel_matrix step1CommonGroup6_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope6.sourceIndex step1CommonScope6_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope6.sourceIndex step1CommonScope6_valid a))) step1CommonPoint6 = true)
kernel_matrix step1CommonGroup6_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope6.neighborIndex step1CommonScope6_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope6.neighborIndex step1CommonScope6_valid b))) step1CommonPoint6 = true)
def step1CommonGroup6 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope6 step1CommonScope6_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint6
  (fun a => step1CommonGroup6_sources a 0) (fun b => step1CommonGroup6_neighbors b 0)

def step1CommonScope7 : Scope := ⟨0, 64, 48, 8⟩
theorem step1CommonScope7_valid : step1CommonScope7.Valid 64 64 := by decide +kernel

def step1CommonPoint7 : CommonPoint.Point := ⟨3107, 1382, 1000⟩
kernel_matrix step1CommonGroup7_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope7.sourceIndex step1CommonScope7_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope7.sourceIndex step1CommonScope7_valid a))) step1CommonPoint7 = true)
kernel_matrix step1CommonGroup7_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope7.neighborIndex step1CommonScope7_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope7.neighborIndex step1CommonScope7_valid b))) step1CommonPoint7 = true)
def step1CommonGroup7 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope7 step1CommonScope7_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint7
  (fun a => step1CommonGroup7_sources a 0) (fun b => step1CommonGroup7_neighbors b 0)

def step1CommonScope8 : Scope := ⟨0, 64, 56, 4⟩
theorem step1CommonScope8_valid : step1CommonScope8.Valid 64 64 := by decide +kernel

def step1CommonPoint8 : CommonPoint.Point := ⟨3119, 1402, 1000⟩
kernel_matrix step1CommonGroup8_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope8.sourceIndex step1CommonScope8_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope8.sourceIndex step1CommonScope8_valid a))) step1CommonPoint8 = true)
kernel_matrix step1CommonGroup8_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope8.neighborIndex step1CommonScope8_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope8.neighborIndex step1CommonScope8_valid b))) step1CommonPoint8 = true)
def step1CommonGroup8 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope8 step1CommonScope8_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint8
  (fun a => step1CommonGroup8_sources a 0) (fun b => step1CommonGroup8_neighbors b 0)

def step1CommonScope9 : Scope := ⟨0, 32, 60, 4⟩
theorem step1CommonScope9_valid : step1CommonScope9.Valid 64 64 := by decide +kernel

kernel_matrix step1CommonGroup9_checked : 32 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step1CommonRawSources (step1CommonScope9.sourceIndex step1CommonScope9_valid a))
    (step1CommonRawNeighbors (step1CommonScope9.neighborIndex step1CommonScope9_valid b))
    (fanDirectionKey (step1CommonSourceAngles (step1CommonScope9.sourceIndex step1CommonScope9_valid a))
      (step1CommonNeighborAngles (step1CommonScope9.neighborIndex step1CommonScope9_valid b))) (fun key => (key + 128) % 256))
def step1CommonGroup9 : CheckedGroup step1Sources step1Neighbors := fallbackGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope9 step1CommonScope9_valid
  step1CommonSourceAngles step1CommonNeighborAngles
  step1CommonSourceAngles_exact step1CommonNeighborAngles_exact
  step1CommonGroup9_checked

def step1CommonScope10 : Scope := ⟨32, 16, 60, 2⟩
theorem step1CommonScope10_valid : step1CommonScope10.Valid 64 64 := by decide +kernel

def step1CommonPoint10 : CommonPoint.Point := ⟨629, 299, 200⟩
kernel_matrix step1CommonGroup10_sources : 16 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope10.sourceIndex step1CommonScope10_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope10.sourceIndex step1CommonScope10_valid a))) step1CommonPoint10 = true)
kernel_matrix step1CommonGroup10_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope10.neighborIndex step1CommonScope10_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope10.neighborIndex step1CommonScope10_valid b))) step1CommonPoint10 = true)
def step1CommonGroup10 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope10 step1CommonScope10_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint10
  (fun a => step1CommonGroup10_sources a 0) (fun b => step1CommonGroup10_neighbors b 0)

def step1CommonScope11 : Scope := ⟨32, 16, 62, 2⟩
theorem step1CommonScope11_valid : step1CommonScope11.Valid 64 64 := by decide +kernel

kernel_matrix step1CommonGroup11_checked : 16 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step1CommonRawSources (step1CommonScope11.sourceIndex step1CommonScope11_valid a))
    (step1CommonRawNeighbors (step1CommonScope11.neighborIndex step1CommonScope11_valid b))
    (fanDirectionKey (step1CommonSourceAngles (step1CommonScope11.sourceIndex step1CommonScope11_valid a))
      (step1CommonNeighborAngles (step1CommonScope11.neighborIndex step1CommonScope11_valid b))) (fun key => (key + 128) % 256))
def step1CommonGroup11 : CheckedGroup step1Sources step1Neighbors := fallbackGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope11 step1CommonScope11_valid
  step1CommonSourceAngles step1CommonNeighborAngles
  step1CommonSourceAngles_exact step1CommonNeighborAngles_exact
  step1CommonGroup11_checked

def step1CommonScope12 : Scope := ⟨48, 16, 60, 4⟩
theorem step1CommonScope12_valid : step1CommonScope12.Valid 64 64 := by decide +kernel

def step1CommonPoint12 : CommonPoint.Point := ⟨15213, 8041, 5000⟩
kernel_matrix step1CommonGroup12_sources : 16 × 1 => (fun a _ =>
  CommonPoint.check (step1CommonRawSources (step1CommonScope12.sourceIndex step1CommonScope12_valid a))
    (ownKeys (step1CommonSourceAngles (step1CommonScope12.sourceIndex step1CommonScope12_valid a))) step1CommonPoint12 = true)
kernel_matrix step1CommonGroup12_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step1CommonRawNeighbors (step1CommonScope12.neighborIndex step1CommonScope12_valid b))
    (ownKeys (step1CommonNeighborAngles (step1CommonScope12.neighborIndex step1CommonScope12_valid b))) step1CommonPoint12 = true)
def step1CommonGroup12 : CheckedGroup step1Sources step1Neighbors := pointGroup
  step1Sources step1Neighbors
  step1CommonRawSources step1CommonRawNeighbors
  step1CommonRawSources_exact step1CommonRawNeighbors_exact
  step1CommonNeighborUnblocked step1CommonScope12 step1CommonScope12_valid
  (fun i => ownKeys (step1CommonSourceAngles i))
  (fun j => ownKeys (step1CommonNeighborAngles j)) step1CommonPoint12
  (fun a => step1CommonGroup12_sources a 0) (fun b => step1CommonGroup12_neighbors b 0)

def step1CommonScopes : List Scope := [
  step1CommonScope0, step1CommonScope1, step1CommonScope2, step1CommonScope3, step1CommonScope4, step1CommonScope5, step1CommonScope6, step1CommonScope7, step1CommonScope8, step1CommonScope9, step1CommonScope10, step1CommonScope11, step1CommonScope12]
def step1CommonGroups : List (CheckedGroup step1Sources step1Neighbors) := [
  step1CommonGroup0, step1CommonGroup1, step1CommonGroup2, step1CommonGroup3, step1CommonGroup4, step1CommonGroup5, step1CommonGroup6, step1CommonGroup7, step1CommonGroup8, step1CommonGroup9, step1CommonGroup10, step1CommonGroup11, step1CommonGroup12]
theorem step1CommonScopes_exact :
    step1CommonGroups.map CheckedGroup.scope = step1CommonScopes := rfl
kernel_matrix step1CommonCoverage : 64 × 64 => (fun i j =>
  ScopeCheck step1CommonScopes i.val j.val)
theorem step1_geometric_overlap (i : Fin 64) (j : Fin 64) :
    PairOverlaps (step1Sources i) (step1Neighbors j) :=
  groups_sound step1Sources step1Neighbors step1CommonGroups
    step1CommonScopes step1CommonScopes_exact step1CommonCoverage i j
#print axioms step1_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
