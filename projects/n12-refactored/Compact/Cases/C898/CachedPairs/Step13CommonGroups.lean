import Compact.Cases.C898.CachedPairs.Step13CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step13CommonScope0 : Scope := ⟨0, 5, 0, 3⟩
theorem step13CommonScope0_valid : step13CommonScope0.Valid 23 63 := by decide +kernel

kernel_matrix step13CommonGroup0_checked : 5 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step13CommonRawSources (step13CommonScope0.sourceIndex step13CommonScope0_valid a))
    (step13CommonRawNeighbors (step13CommonScope0.neighborIndex step13CommonScope0_valid b))
    (fanDirectionKey (step13CommonSourceAngles (step13CommonScope0.sourceIndex step13CommonScope0_valid a))
      (step13CommonNeighborAngles (step13CommonScope0.neighborIndex step13CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step13CommonGroup0 : CheckedGroup step13Sources step13Neighbors := fallbackGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope0 step13CommonScope0_valid
  step13CommonSourceAngles step13CommonNeighborAngles
  step13CommonSourceAngles_exact step13CommonNeighborAngles_exact
  step13CommonGroup0_checked

def step13CommonScope1 : Scope := ⟨0, 5, 3, 2⟩
theorem step13CommonScope1_valid : step13CommonScope1.Valid 23 63 := by decide +kernel

def step13CommonPoint1 : CommonPoint.Point := ⟨2028, 2037, 1000⟩
kernel_matrix step13CommonGroup1_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope1.sourceIndex step13CommonScope1_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope1.sourceIndex step13CommonScope1_valid a))) step13CommonPoint1 = true)
kernel_matrix step13CommonGroup1_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope1.neighborIndex step13CommonScope1_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope1.neighborIndex step13CommonScope1_valid b))) step13CommonPoint1 = true)
def step13CommonGroup1 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope1 step13CommonScope1_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint1
  (fun a => step13CommonGroup1_sources a 0) (fun b => step13CommonGroup1_neighbors b 0)

def step13CommonScope2 : Scope := ⟨0, 5, 5, 2⟩
theorem step13CommonScope2_valid : step13CommonScope2.Valid 23 63 := by decide +kernel

def step13CommonPoint2 : CommonPoint.Point := ⟨512, 511, 250⟩
kernel_matrix step13CommonGroup2_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope2.sourceIndex step13CommonScope2_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope2.sourceIndex step13CommonScope2_valid a))) step13CommonPoint2 = true)
kernel_matrix step13CommonGroup2_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope2.neighborIndex step13CommonScope2_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope2.neighborIndex step13CommonScope2_valid b))) step13CommonPoint2 = true)
def step13CommonGroup2 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope2 step13CommonScope2_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint2
  (fun a => step13CommonGroup2_sources a 0) (fun b => step13CommonGroup2_neighbors b 0)

def step13CommonScope3 : Scope := ⟨5, 6, 0, 3⟩
theorem step13CommonScope3_valid : step13CommonScope3.Valid 23 63 := by decide +kernel

kernel_matrix step13CommonGroup3_checked : 6 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step13CommonRawSources (step13CommonScope3.sourceIndex step13CommonScope3_valid a))
    (step13CommonRawNeighbors (step13CommonScope3.neighborIndex step13CommonScope3_valid b))
    (fanDirectionKey (step13CommonSourceAngles (step13CommonScope3.sourceIndex step13CommonScope3_valid a))
      (step13CommonNeighborAngles (step13CommonScope3.neighborIndex step13CommonScope3_valid b))) (fun key => (key + 128) % 256))
def step13CommonGroup3 : CheckedGroup step13Sources step13Neighbors := fallbackGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope3 step13CommonScope3_valid
  step13CommonSourceAngles step13CommonNeighborAngles
  step13CommonSourceAngles_exact step13CommonNeighborAngles_exact
  step13CommonGroup3_checked

def step13CommonScope4 : Scope := ⟨5, 6, 3, 4⟩
theorem step13CommonScope4_valid : step13CommonScope4.Valid 23 63 := by decide +kernel

def step13CommonPoint4 : CommonPoint.Point := ⟨507, 510, 250⟩
kernel_matrix step13CommonGroup4_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope4.sourceIndex step13CommonScope4_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope4.sourceIndex step13CommonScope4_valid a))) step13CommonPoint4 = true)
kernel_matrix step13CommonGroup4_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope4.neighborIndex step13CommonScope4_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope4.neighborIndex step13CommonScope4_valid b))) step13CommonPoint4 = true)
def step13CommonGroup4 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope4 step13CommonScope4_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint4
  (fun a => step13CommonGroup4_sources a 0) (fun b => step13CommonGroup4_neighbors b 0)

def step13CommonScope5 : Scope := ⟨0, 11, 7, 8⟩
theorem step13CommonScope5_valid : step13CommonScope5.Valid 23 63 := by decide +kernel

def step13CommonPoint5 : CommonPoint.Point := ⟨1037223, 1027590, 500000⟩
kernel_matrix step13CommonGroup5_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope5.sourceIndex step13CommonScope5_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope5.sourceIndex step13CommonScope5_valid a))) step13CommonPoint5 = true)
kernel_matrix step13CommonGroup5_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope5.neighborIndex step13CommonScope5_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope5.neighborIndex step13CommonScope5_valid b))) step13CommonPoint5 = true)
def step13CommonGroup5 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope5 step13CommonScope5_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint5
  (fun a => step13CommonGroup5_sources a 0) (fun b => step13CommonGroup5_neighbors b 0)

def step13CommonScope6 : Scope := ⟨0, 11, 15, 16⟩
theorem step13CommonScope6_valid : step13CommonScope6.Valid 23 63 := by decide +kernel

def step13CommonPoint6 : CommonPoint.Point := ⟨2009, 2025, 1000⟩
kernel_matrix step13CommonGroup6_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope6.sourceIndex step13CommonScope6_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope6.sourceIndex step13CommonScope6_valid a))) step13CommonPoint6 = true)
kernel_matrix step13CommonGroup6_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope6.neighborIndex step13CommonScope6_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope6.neighborIndex step13CommonScope6_valid b))) step13CommonPoint6 = true)
def step13CommonGroup6 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope6 step13CommonScope6_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint6
  (fun a => step13CommonGroup6_sources a 0) (fun b => step13CommonGroup6_neighbors b 0)

def step13CommonScope7 : Scope := ⟨11, 12, 0, 31⟩
theorem step13CommonScope7_valid : step13CommonScope7.Valid 23 63 := by decide +kernel

def step13CommonPoint7 : CommonPoint.Point := ⟨1984, 2033, 1000⟩
kernel_matrix step13CommonGroup7_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope7.sourceIndex step13CommonScope7_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope7.sourceIndex step13CommonScope7_valid a))) step13CommonPoint7 = true)
kernel_matrix step13CommonGroup7_neighbors : 31 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope7.neighborIndex step13CommonScope7_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope7.neighborIndex step13CommonScope7_valid b))) step13CommonPoint7 = true)
def step13CommonGroup7 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope7 step13CommonScope7_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint7
  (fun a => step13CommonGroup7_sources a 0) (fun b => step13CommonGroup7_neighbors b 0)

def step13CommonScope8 : Scope := ⟨0, 23, 31, 16⟩
theorem step13CommonScope8_valid : step13CommonScope8.Valid 23 63 := by decide +kernel

def step13CommonPoint8 : CommonPoint.Point := ⟨917, 948, 500⟩
kernel_matrix step13CommonGroup8_sources : 23 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope8.sourceIndex step13CommonScope8_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope8.sourceIndex step13CommonScope8_valid a))) step13CommonPoint8 = true)
kernel_matrix step13CommonGroup8_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope8.neighborIndex step13CommonScope8_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope8.neighborIndex step13CommonScope8_valid b))) step13CommonPoint8 = true)
def step13CommonGroup8 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope8 step13CommonScope8_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint8
  (fun a => step13CommonGroup8_sources a 0) (fun b => step13CommonGroup8_neighbors b 0)

def step13CommonScope9 : Scope := ⟨0, 11, 47, 8⟩
theorem step13CommonScope9_valid : step13CommonScope9.Valid 23 63 := by decide +kernel

def step13CommonPoint9 : CommonPoint.Point := ⟨959, 976, 500⟩
kernel_matrix step13CommonGroup9_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope9.sourceIndex step13CommonScope9_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope9.sourceIndex step13CommonScope9_valid a))) step13CommonPoint9 = true)
kernel_matrix step13CommonGroup9_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope9.neighborIndex step13CommonScope9_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope9.neighborIndex step13CommonScope9_valid b))) step13CommonPoint9 = true)
def step13CommonGroup9 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope9 step13CommonScope9_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint9
  (fun a => step13CommonGroup9_sources a 0) (fun b => step13CommonGroup9_neighbors b 0)

def step13CommonScope10 : Scope := ⟨0, 11, 55, 4⟩
theorem step13CommonScope10_valid : step13CommonScope10.Valid 23 63 := by decide +kernel

def step13CommonPoint10 : CommonPoint.Point := ⟨1950, 1981, 1000⟩
kernel_matrix step13CommonGroup10_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope10.sourceIndex step13CommonScope10_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope10.sourceIndex step13CommonScope10_valid a))) step13CommonPoint10 = true)
kernel_matrix step13CommonGroup10_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope10.neighborIndex step13CommonScope10_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope10.neighborIndex step13CommonScope10_valid b))) step13CommonPoint10 = true)
def step13CommonGroup10 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope10 step13CommonScope10_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint10
  (fun a => step13CommonGroup10_sources a 0) (fun b => step13CommonGroup10_neighbors b 0)

def step13CommonScope11 : Scope := ⟨0, 11, 59, 4⟩
theorem step13CommonScope11_valid : step13CommonScope11.Valid 23 63 := by decide +kernel

def step13CommonPoint11 : CommonPoint.Point := ⟨1976, 2007, 1000⟩
kernel_matrix step13CommonGroup11_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope11.sourceIndex step13CommonScope11_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope11.sourceIndex step13CommonScope11_valid a))) step13CommonPoint11 = true)
kernel_matrix step13CommonGroup11_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope11.neighborIndex step13CommonScope11_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope11.neighborIndex step13CommonScope11_valid b))) step13CommonPoint11 = true)
def step13CommonGroup11 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope11 step13CommonScope11_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint11
  (fun a => step13CommonGroup11_sources a 0) (fun b => step13CommonGroup11_neighbors b 0)

def step13CommonScope12 : Scope := ⟨11, 12, 47, 16⟩
theorem step13CommonScope12_valid : step13CommonScope12.Valid 23 63 := by decide +kernel

def step13CommonPoint12 : CommonPoint.Point := ⟨1953, 2011, 1000⟩
kernel_matrix step13CommonGroup12_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step13CommonRawSources (step13CommonScope12.sourceIndex step13CommonScope12_valid a))
    (ownKeys (step13CommonSourceAngles (step13CommonScope12.sourceIndex step13CommonScope12_valid a))) step13CommonPoint12 = true)
kernel_matrix step13CommonGroup12_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step13CommonRawNeighbors (step13CommonScope12.neighborIndex step13CommonScope12_valid b))
    (ownKeys (step13CommonNeighborAngles (step13CommonScope12.neighborIndex step13CommonScope12_valid b))) step13CommonPoint12 = true)
def step13CommonGroup12 : CheckedGroup step13Sources step13Neighbors := pointGroup
  step13Sources step13Neighbors
  step13CommonRawSources step13CommonRawNeighbors
  step13CommonRawSources_exact step13CommonRawNeighbors_exact
  step13CommonNeighborUnblocked step13CommonScope12 step13CommonScope12_valid
  (fun i => ownKeys (step13CommonSourceAngles i))
  (fun j => ownKeys (step13CommonNeighborAngles j)) step13CommonPoint12
  (fun a => step13CommonGroup12_sources a 0) (fun b => step13CommonGroup12_neighbors b 0)

def step13CommonScopes : List Scope := [
  step13CommonScope0, step13CommonScope1, step13CommonScope2, step13CommonScope3, step13CommonScope4, step13CommonScope5, step13CommonScope6, step13CommonScope7, step13CommonScope8, step13CommonScope9, step13CommonScope10, step13CommonScope11, step13CommonScope12]
def step13CommonGroups : List (CheckedGroup step13Sources step13Neighbors) := [
  step13CommonGroup0, step13CommonGroup1, step13CommonGroup2, step13CommonGroup3, step13CommonGroup4, step13CommonGroup5, step13CommonGroup6, step13CommonGroup7, step13CommonGroup8, step13CommonGroup9, step13CommonGroup10, step13CommonGroup11, step13CommonGroup12]
theorem step13CommonScopes_exact :
    step13CommonGroups.map CheckedGroup.scope = step13CommonScopes := rfl
kernel_matrix step13CommonCoverage : 23 × 63 => (fun i j =>
  ScopeCheck step13CommonScopes i.val j.val)
theorem step13_geometric_overlap (i : Fin 23) (j : Fin 63) :
    PairOverlaps (step13Sources i) (step13Neighbors j) :=
  groups_sound step13Sources step13Neighbors step13CommonGroups
    step13CommonScopes step13CommonScopes_exact step13CommonCoverage i j
#print axioms step13_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
