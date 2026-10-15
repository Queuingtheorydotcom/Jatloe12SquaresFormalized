import Compact.Cases.C898.CachedPairs.Step03CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step3CommonScope0 : Scope := ⟨0, 7, 0, 4⟩
theorem step3CommonScope0_valid : step3CommonScope0.Valid 7 64 := by decide +kernel

def step3CommonPoint0 : CommonPoint.Point := ⟨2980, 3019, 1000⟩
kernel_matrix step3CommonGroup0_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope0.sourceIndex step3CommonScope0_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope0.sourceIndex step3CommonScope0_valid a))) step3CommonPoint0 = true)
kernel_matrix step3CommonGroup0_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope0.neighborIndex step3CommonScope0_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope0.neighborIndex step3CommonScope0_valid b))) step3CommonPoint0 = true)
def step3CommonGroup0 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope0 step3CommonScope0_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint0
  (fun a => step3CommonGroup0_sources a 0) (fun b => step3CommonGroup0_neighbors b 0)

def step3CommonScope1 : Scope := ⟨0, 7, 4, 4⟩
theorem step3CommonScope1_valid : step3CommonScope1.Valid 7 64 := by decide +kernel

def step3CommonPoint1 : CommonPoint.Point := ⟨300233, 303050, 100000⟩
kernel_matrix step3CommonGroup1_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope1.sourceIndex step3CommonScope1_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope1.sourceIndex step3CommonScope1_valid a))) step3CommonPoint1 = true)
kernel_matrix step3CommonGroup1_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope1.neighborIndex step3CommonScope1_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope1.neighborIndex step3CommonScope1_valid b))) step3CommonPoint1 = true)
def step3CommonGroup1 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope1 step3CommonScope1_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint1
  (fun a => step3CommonGroup1_sources a 0) (fun b => step3CommonGroup1_neighbors b 0)

def step3CommonScope2 : Scope := ⟨0, 1, 8, 4⟩
theorem step3CommonScope2_valid : step3CommonScope2.Valid 7 64 := by decide +kernel

def step3CommonPoint2 : CommonPoint.Point := ⟨6583621, 7330900, 2500000⟩
kernel_matrix step3CommonGroup2_sources : 1 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope2.sourceIndex step3CommonScope2_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope2.sourceIndex step3CommonScope2_valid a))) step3CommonPoint2 = true)
kernel_matrix step3CommonGroup2_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope2.neighborIndex step3CommonScope2_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope2.neighborIndex step3CommonScope2_valid b))) step3CommonPoint2 = true)
def step3CommonGroup2 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope2 step3CommonScope2_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint2
  (fun a => step3CommonGroup2_sources a 0) (fun b => step3CommonGroup2_neighbors b 0)

def step3CommonScope3 : Scope := ⟨1, 2, 8, 4⟩
theorem step3CommonScope3_valid : step3CommonScope3.Valid 7 64 := by decide +kernel

def step3CommonPoint3 : CommonPoint.Point := ⟨29964947, 30313327, 10000000⟩
kernel_matrix step3CommonGroup3_sources : 2 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope3.sourceIndex step3CommonScope3_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope3.sourceIndex step3CommonScope3_valid a))) step3CommonPoint3 = true)
kernel_matrix step3CommonGroup3_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope3.neighborIndex step3CommonScope3_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope3.neighborIndex step3CommonScope3_valid b))) step3CommonPoint3 = true)
def step3CommonGroup3 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope3 step3CommonScope3_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint3
  (fun a => step3CommonGroup3_sources a 0) (fun b => step3CommonGroup3_neighbors b 0)

def step3CommonScope4 : Scope := ⟨3, 4, 8, 2⟩
theorem step3CommonScope4_valid : step3CommonScope4.Valid 7 64 := by decide +kernel

def step3CommonPoint4 : CommonPoint.Point := ⟨608, 609, 200⟩
kernel_matrix step3CommonGroup4_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope4.sourceIndex step3CommonScope4_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope4.sourceIndex step3CommonScope4_valid a))) step3CommonPoint4 = true)
kernel_matrix step3CommonGroup4_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope4.neighborIndex step3CommonScope4_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope4.neighborIndex step3CommonScope4_valid b))) step3CommonPoint4 = true)
def step3CommonGroup4 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope4 step3CommonScope4_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint4
  (fun a => step3CommonGroup4_sources a 0) (fun b => step3CommonGroup4_neighbors b 0)

def step3CommonScope5 : Scope := ⟨3, 2, 10, 2⟩
theorem step3CommonScope5_valid : step3CommonScope5.Valid 7 64 := by decide +kernel

kernel_matrix step3CommonGroup5_checked : 2 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step3CommonRawSources (step3CommonScope5.sourceIndex step3CommonScope5_valid a))
    (step3CommonRawNeighbors (step3CommonScope5.neighborIndex step3CommonScope5_valid b))
    (fanDirectionKey (step3CommonSourceAngles (step3CommonScope5.sourceIndex step3CommonScope5_valid a))
      (step3CommonNeighborAngles (step3CommonScope5.neighborIndex step3CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step3CommonGroup5 : CheckedGroup step3Sources step3Neighbors := fallbackGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope5 step3CommonScope5_valid
  step3CommonSourceAngles step3CommonNeighborAngles
  step3CommonSourceAngles_exact step3CommonNeighborAngles_exact
  step3CommonGroup5_checked

def step3CommonScope6 : Scope := ⟨5, 2, 10, 2⟩
theorem step3CommonScope6_valid : step3CommonScope6.Valid 7 64 := by decide +kernel

def step3CommonPoint6 : CommonPoint.Point := ⟨753, 760, 250⟩
kernel_matrix step3CommonGroup6_sources : 2 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope6.sourceIndex step3CommonScope6_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope6.sourceIndex step3CommonScope6_valid a))) step3CommonPoint6 = true)
kernel_matrix step3CommonGroup6_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope6.neighborIndex step3CommonScope6_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope6.neighborIndex step3CommonScope6_valid b))) step3CommonPoint6 = true)
def step3CommonGroup6 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope6 step3CommonScope6_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint6
  (fun a => step3CommonGroup6_sources a 0) (fun b => step3CommonGroup6_neighbors b 0)

def step3CommonScope7 : Scope := ⟨0, 7, 12, 4⟩
theorem step3CommonScope7_valid : step3CommonScope7.Valid 7 64 := by decide +kernel

def step3CommonPoint7 : CommonPoint.Point := ⟨28717407, 29774766, 10000000⟩
kernel_matrix step3CommonGroup7_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope7.sourceIndex step3CommonScope7_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope7.sourceIndex step3CommonScope7_valid a))) step3CommonPoint7 = true)
kernel_matrix step3CommonGroup7_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope7.neighborIndex step3CommonScope7_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope7.neighborIndex step3CommonScope7_valid b))) step3CommonPoint7 = true)
def step3CommonGroup7 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope7 step3CommonScope7_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint7
  (fun a => step3CommonGroup7_sources a 0) (fun b => step3CommonGroup7_neighbors b 0)

def step3CommonScope8 : Scope := ⟨0, 7, 16, 16⟩
theorem step3CommonScope8_valid : step3CommonScope8.Valid 7 64 := by decide +kernel

def step3CommonPoint8 : CommonPoint.Point := ⟨2799, 2931, 1000⟩
kernel_matrix step3CommonGroup8_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope8.sourceIndex step3CommonScope8_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope8.sourceIndex step3CommonScope8_valid a))) step3CommonPoint8 = true)
kernel_matrix step3CommonGroup8_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope8.neighborIndex step3CommonScope8_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope8.neighborIndex step3CommonScope8_valid b))) step3CommonPoint8 = true)
def step3CommonGroup8 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope8 step3CommonScope8_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint8
  (fun a => step3CommonGroup8_sources a 0) (fun b => step3CommonGroup8_neighbors b 0)

def step3CommonScope9 : Scope := ⟨0, 7, 32, 32⟩
theorem step3CommonScope9_valid : step3CommonScope9.Valid 7 64 := by decide +kernel

def step3CommonPoint9 : CommonPoint.Point := ⟨1487, 1505, 500⟩
kernel_matrix step3CommonGroup9_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step3CommonRawSources (step3CommonScope9.sourceIndex step3CommonScope9_valid a))
    (ownKeys (step3CommonSourceAngles (step3CommonScope9.sourceIndex step3CommonScope9_valid a))) step3CommonPoint9 = true)
kernel_matrix step3CommonGroup9_neighbors : 32 × 1 => (fun b _ =>
  CommonPoint.check (step3CommonRawNeighbors (step3CommonScope9.neighborIndex step3CommonScope9_valid b))
    (ownKeys (step3CommonNeighborAngles (step3CommonScope9.neighborIndex step3CommonScope9_valid b))) step3CommonPoint9 = true)
def step3CommonGroup9 : CheckedGroup step3Sources step3Neighbors := pointGroup
  step3Sources step3Neighbors
  step3CommonRawSources step3CommonRawNeighbors
  step3CommonRawSources_exact step3CommonRawNeighbors_exact
  step3CommonNeighborUnblocked step3CommonScope9 step3CommonScope9_valid
  (fun i => ownKeys (step3CommonSourceAngles i))
  (fun j => ownKeys (step3CommonNeighborAngles j)) step3CommonPoint9
  (fun a => step3CommonGroup9_sources a 0) (fun b => step3CommonGroup9_neighbors b 0)

def step3CommonScopes : List Scope := [
  step3CommonScope0, step3CommonScope1, step3CommonScope2, step3CommonScope3, step3CommonScope4, step3CommonScope5, step3CommonScope6, step3CommonScope7, step3CommonScope8, step3CommonScope9]
def step3CommonGroups : List (CheckedGroup step3Sources step3Neighbors) := [
  step3CommonGroup0, step3CommonGroup1, step3CommonGroup2, step3CommonGroup3, step3CommonGroup4, step3CommonGroup5, step3CommonGroup6, step3CommonGroup7, step3CommonGroup8, step3CommonGroup9]
theorem step3CommonScopes_exact :
    step3CommonGroups.map CheckedGroup.scope = step3CommonScopes := rfl
kernel_matrix step3CommonCoverage : 7 × 64 => (fun i j =>
  ScopeCheck step3CommonScopes i.val j.val)
theorem step3_geometric_overlap (i : Fin 7) (j : Fin 64) :
    PairOverlaps (step3Sources i) (step3Neighbors j) :=
  groups_sound step3Sources step3Neighbors step3CommonGroups
    step3CommonScopes step3CommonScopes_exact step3CommonCoverage i j
#print axioms step3_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
