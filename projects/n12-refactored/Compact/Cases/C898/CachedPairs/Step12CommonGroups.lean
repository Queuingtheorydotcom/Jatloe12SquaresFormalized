import Compact.Cases.C898.CachedPairs.Step12CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step12CommonScope0 : Scope := ⟨0, 12, 0, 6⟩
theorem step12CommonScope0_valid : step12CommonScope0.Valid 49 12 := by decide +kernel

def step12CommonPoint0 : CommonPoint.Point := ⟨2439, 2027, 1000⟩
kernel_matrix step12CommonGroup0_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope0.sourceIndex step12CommonScope0_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope0.sourceIndex step12CommonScope0_valid a))) step12CommonPoint0 = true)
kernel_matrix step12CommonGroup0_neighbors : 6 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope0.neighborIndex step12CommonScope0_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope0.neighborIndex step12CommonScope0_valid b))) step12CommonPoint0 = true)
def step12CommonGroup0 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope0 step12CommonScope0_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint0
  (fun a => step12CommonGroup0_sources a 0) (fun b => step12CommonGroup0_neighbors b 0)

def step12CommonScope1 : Scope := ⟨0, 6, 6, 6⟩
theorem step12CommonScope1_valid : step12CommonScope1.Valid 49 12 := by decide +kernel

def step12CommonPoint1 : CommonPoint.Point := ⟨2474, 2037, 1000⟩
kernel_matrix step12CommonGroup1_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope1.sourceIndex step12CommonScope1_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope1.sourceIndex step12CommonScope1_valid a))) step12CommonPoint1 = true)
kernel_matrix step12CommonGroup1_neighbors : 6 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope1.neighborIndex step12CommonScope1_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope1.neighborIndex step12CommonScope1_valid b))) step12CommonPoint1 = true)
def step12CommonGroup1 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope1 step12CommonScope1_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint1
  (fun a => step12CommonGroup1_sources a 0) (fun b => step12CommonGroup1_neighbors b 0)

def step12CommonScope2 : Scope := ⟨6, 6, 6, 3⟩
theorem step12CommonScope2_valid : step12CommonScope2.Valid 49 12 := by decide +kernel

def step12CommonPoint2 : CommonPoint.Point := ⟨620, 489, 250⟩
kernel_matrix step12CommonGroup2_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope2.sourceIndex step12CommonScope2_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope2.sourceIndex step12CommonScope2_valid a))) step12CommonPoint2 = true)
kernel_matrix step12CommonGroup2_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope2.neighborIndex step12CommonScope2_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope2.neighborIndex step12CommonScope2_valid b))) step12CommonPoint2 = true)
def step12CommonGroup2 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope2 step12CommonScope2_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint2
  (fun a => step12CommonGroup2_sources a 0) (fun b => step12CommonGroup2_neighbors b 0)

def step12CommonScope3 : Scope := ⟨6, 3, 9, 3⟩
theorem step12CommonScope3_valid : step12CommonScope3.Valid 49 12 := by decide +kernel

def step12CommonPoint3 : CommonPoint.Point := ⟨2473, 2041, 1000⟩
kernel_matrix step12CommonGroup3_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope3.sourceIndex step12CommonScope3_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope3.sourceIndex step12CommonScope3_valid a))) step12CommonPoint3 = true)
kernel_matrix step12CommonGroup3_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope3.neighborIndex step12CommonScope3_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope3.neighborIndex step12CommonScope3_valid b))) step12CommonPoint3 = true)
def step12CommonGroup3 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope3 step12CommonScope3_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint3
  (fun a => step12CommonGroup3_sources a 0) (fun b => step12CommonGroup3_neighbors b 0)

def step12CommonScope4 : Scope := ⟨9, 3, 9, 1⟩
theorem step12CommonScope4_valid : step12CommonScope4.Valid 49 12 := by decide +kernel

def step12CommonPoint4 : CommonPoint.Point := ⟨2510, 1893, 1000⟩
kernel_matrix step12CommonGroup4_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope4.sourceIndex step12CommonScope4_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope4.sourceIndex step12CommonScope4_valid a))) step12CommonPoint4 = true)
kernel_matrix step12CommonGroup4_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope4.neighborIndex step12CommonScope4_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope4.neighborIndex step12CommonScope4_valid b))) step12CommonPoint4 = true)
def step12CommonGroup4 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope4 step12CommonScope4_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint4
  (fun a => step12CommonGroup4_sources a 0) (fun b => step12CommonGroup4_neighbors b 0)

def step12CommonScope5 : Scope := ⟨9, 3, 10, 2⟩
theorem step12CommonScope5_valid : step12CommonScope5.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup5_checked : 3 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope5.sourceIndex step12CommonScope5_valid a))
    (step12CommonRawNeighbors (step12CommonScope5.neighborIndex step12CommonScope5_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope5.sourceIndex step12CommonScope5_valid a))
      (step12CommonNeighborAngles (step12CommonScope5.neighborIndex step12CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup5 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope5 step12CommonScope5_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup5_checked

def step12CommonScope6 : Scope := ⟨12, 6, 0, 3⟩
theorem step12CommonScope6_valid : step12CommonScope6.Valid 49 12 := by decide +kernel

def step12CommonPoint6 : CommonPoint.Point := ⟨1201, 1013, 500⟩
kernel_matrix step12CommonGroup6_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope6.sourceIndex step12CommonScope6_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope6.sourceIndex step12CommonScope6_valid a))) step12CommonPoint6 = true)
kernel_matrix step12CommonGroup6_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope6.neighborIndex step12CommonScope6_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope6.neighborIndex step12CommonScope6_valid b))) step12CommonPoint6 = true)
def step12CommonGroup6 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope6 step12CommonScope6_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint6
  (fun a => step12CommonGroup6_sources a 0) (fun b => step12CommonGroup6_neighbors b 0)

def step12CommonScope7 : Scope := ⟨12, 6, 3, 3⟩
theorem step12CommonScope7_valid : step12CommonScope7.Valid 49 12 := by decide +kernel

def step12CommonPoint7 : CommonPoint.Point := ⟨2438, 1977, 1000⟩
kernel_matrix step12CommonGroup7_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope7.sourceIndex step12CommonScope7_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope7.sourceIndex step12CommonScope7_valid a))) step12CommonPoint7 = true)
kernel_matrix step12CommonGroup7_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope7.neighborIndex step12CommonScope7_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope7.neighborIndex step12CommonScope7_valid b))) step12CommonPoint7 = true)
def step12CommonGroup7 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope7 step12CommonScope7_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint7
  (fun a => step12CommonGroup7_sources a 0) (fun b => step12CommonGroup7_neighbors b 0)

def step12CommonScope8 : Scope := ⟨18, 3, 0, 3⟩
theorem step12CommonScope8_valid : step12CommonScope8.Valid 49 12 := by decide +kernel

def step12CommonPoint8 : CommonPoint.Point := ⟨599, 503, 250⟩
kernel_matrix step12CommonGroup8_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope8.sourceIndex step12CommonScope8_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope8.sourceIndex step12CommonScope8_valid a))) step12CommonPoint8 = true)
kernel_matrix step12CommonGroup8_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope8.neighborIndex step12CommonScope8_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope8.neighborIndex step12CommonScope8_valid b))) step12CommonPoint8 = true)
def step12CommonGroup8 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope8 step12CommonScope8_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint8
  (fun a => step12CommonGroup8_sources a 0) (fun b => step12CommonGroup8_neighbors b 0)

def step12CommonScope9 : Scope := ⟨21, 3, 0, 1⟩
theorem step12CommonScope9_valid : step12CommonScope9.Valid 49 12 := by decide +kernel

def step12CommonPoint9 : CommonPoint.Point := ⟨1187, 1005, 500⟩
kernel_matrix step12CommonGroup9_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope9.sourceIndex step12CommonScope9_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope9.sourceIndex step12CommonScope9_valid a))) step12CommonPoint9 = true)
kernel_matrix step12CommonGroup9_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope9.neighborIndex step12CommonScope9_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope9.neighborIndex step12CommonScope9_valid b))) step12CommonPoint9 = true)
def step12CommonGroup9 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope9 step12CommonScope9_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint9
  (fun a => step12CommonGroup9_sources a 0) (fun b => step12CommonGroup9_neighbors b 0)

def step12CommonScope10 : Scope := ⟨21, 3, 1, 2⟩
theorem step12CommonScope10_valid : step12CommonScope10.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup10_checked : 3 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope10.sourceIndex step12CommonScope10_valid a))
    (step12CommonRawNeighbors (step12CommonScope10.neighborIndex step12CommonScope10_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope10.sourceIndex step12CommonScope10_valid a))
      (step12CommonNeighborAngles (step12CommonScope10.neighborIndex step12CommonScope10_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup10 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope10 step12CommonScope10_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup10_checked

def step12CommonScope11 : Scope := ⟨18, 6, 3, 1⟩
theorem step12CommonScope11_valid : step12CommonScope11.Valid 49 12 := by decide +kernel

def step12CommonPoint11 : CommonPoint.Point := ⟨2413, 1965, 1000⟩
kernel_matrix step12CommonGroup11_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope11.sourceIndex step12CommonScope11_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope11.sourceIndex step12CommonScope11_valid a))) step12CommonPoint11 = true)
kernel_matrix step12CommonGroup11_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope11.neighborIndex step12CommonScope11_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope11.neighborIndex step12CommonScope11_valid b))) step12CommonPoint11 = true)
def step12CommonGroup11 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope11 step12CommonScope11_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint11
  (fun a => step12CommonGroup11_sources a 0) (fun b => step12CommonGroup11_neighbors b 0)

def step12CommonScope12 : Scope := ⟨18, 6, 4, 2⟩
theorem step12CommonScope12_valid : step12CommonScope12.Valid 49 12 := by decide +kernel

def step12CommonPoint12 : CommonPoint.Point := ⟨2437, 1944, 1000⟩
kernel_matrix step12CommonGroup12_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope12.sourceIndex step12CommonScope12_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope12.sourceIndex step12CommonScope12_valid a))) step12CommonPoint12 = true)
kernel_matrix step12CommonGroup12_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope12.neighborIndex step12CommonScope12_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope12.neighborIndex step12CommonScope12_valid b))) step12CommonPoint12 = true)
def step12CommonGroup12 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope12 step12CommonScope12_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint12
  (fun a => step12CommonGroup12_sources a 0) (fun b => step12CommonGroup12_neighbors b 0)

def step12CommonScope13 : Scope := ⟨12, 6, 6, 3⟩
theorem step12CommonScope13_valid : step12CommonScope13.Valid 49 12 := by decide +kernel

def step12CommonPoint13 : CommonPoint.Point := ⟨2485, 1917, 1000⟩
kernel_matrix step12CommonGroup13_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope13.sourceIndex step12CommonScope13_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope13.sourceIndex step12CommonScope13_valid a))) step12CommonPoint13 = true)
kernel_matrix step12CommonGroup13_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope13.neighborIndex step12CommonScope13_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope13.neighborIndex step12CommonScope13_valid b))) step12CommonPoint13 = true)
def step12CommonGroup13 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope13 step12CommonScope13_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint13
  (fun a => step12CommonGroup13_sources a 0) (fun b => step12CommonGroup13_neighbors b 0)

def step12CommonScope14 : Scope := ⟨12, 6, 9, 1⟩
theorem step12CommonScope14_valid : step12CommonScope14.Valid 49 12 := by decide +kernel

def step12CommonPoint14 : CommonPoint.Point := ⟨1258, 933, 500⟩
kernel_matrix step12CommonGroup14_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope14.sourceIndex step12CommonScope14_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope14.sourceIndex step12CommonScope14_valid a))) step12CommonPoint14 = true)
kernel_matrix step12CommonGroup14_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope14.neighborIndex step12CommonScope14_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope14.neighborIndex step12CommonScope14_valid b))) step12CommonPoint14 = true)
def step12CommonGroup14 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope14 step12CommonScope14_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint14
  (fun a => step12CommonGroup14_sources a 0) (fun b => step12CommonGroup14_neighbors b 0)

def step12CommonScope15 : Scope := ⟨12, 6, 10, 1⟩
theorem step12CommonScope15_valid : step12CommonScope15.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup15_checked : 6 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope15.sourceIndex step12CommonScope15_valid a))
    (step12CommonRawNeighbors (step12CommonScope15.neighborIndex step12CommonScope15_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope15.sourceIndex step12CommonScope15_valid a))
      (step12CommonNeighborAngles (step12CommonScope15.neighborIndex step12CommonScope15_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup15 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope15 step12CommonScope15_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup15_checked

def step12CommonScope16 : Scope := ⟨12, 6, 11, 1⟩
theorem step12CommonScope16_valid : step12CommonScope16.Valid 49 12 := by decide +kernel

def step12CommonPoint16 : CommonPoint.Point := ⟨2379, 2042, 1000⟩
kernel_matrix step12CommonGroup16_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope16.sourceIndex step12CommonScope16_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope16.sourceIndex step12CommonScope16_valid a))) step12CommonPoint16 = true)
kernel_matrix step12CommonGroup16_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope16.neighborIndex step12CommonScope16_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope16.neighborIndex step12CommonScope16_valid b))) step12CommonPoint16 = true)
def step12CommonGroup16 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope16 step12CommonScope16_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint16
  (fun a => step12CommonGroup16_sources a 0) (fun b => step12CommonGroup16_neighbors b 0)

def step12CommonScope17 : Scope := ⟨18, 6, 6, 1⟩
theorem step12CommonScope17_valid : step12CommonScope17.Valid 49 12 := by decide +kernel

def step12CommonPoint17 : CommonPoint.Point := ⟨615, 479, 250⟩
kernel_matrix step12CommonGroup17_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope17.sourceIndex step12CommonScope17_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope17.sourceIndex step12CommonScope17_valid a))) step12CommonPoint17 = true)
kernel_matrix step12CommonGroup17_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope17.neighborIndex step12CommonScope17_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope17.neighborIndex step12CommonScope17_valid b))) step12CommonPoint17 = true)
def step12CommonGroup17 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope17 step12CommonScope17_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint17
  (fun a => step12CommonGroup17_sources a 0) (fun b => step12CommonGroup17_neighbors b 0)

def step12CommonScope18 : Scope := ⟨18, 6, 7, 1⟩
theorem step12CommonScope18_valid : step12CommonScope18.Valid 49 12 := by decide +kernel

def step12CommonPoint18 : CommonPoint.Point := ⟨2477, 1898, 1000⟩
kernel_matrix step12CommonGroup18_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope18.sourceIndex step12CommonScope18_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope18.sourceIndex step12CommonScope18_valid a))) step12CommonPoint18 = true)
kernel_matrix step12CommonGroup18_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope18.neighborIndex step12CommonScope18_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope18.neighborIndex step12CommonScope18_valid b))) step12CommonPoint18 = true)
def step12CommonGroup18 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope18 step12CommonScope18_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint18
  (fun a => step12CommonGroup18_sources a 0) (fun b => step12CommonGroup18_neighbors b 0)

def step12CommonScope19 : Scope := ⟨18, 6, 8, 1⟩
theorem step12CommonScope19_valid : step12CommonScope19.Valid 49 12 := by decide +kernel

def step12CommonPoint19 : CommonPoint.Point := ⟨312, 235, 125⟩
kernel_matrix step12CommonGroup19_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope19.sourceIndex step12CommonScope19_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope19.sourceIndex step12CommonScope19_valid a))) step12CommonPoint19 = true)
kernel_matrix step12CommonGroup19_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope19.neighborIndex step12CommonScope19_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope19.neighborIndex step12CommonScope19_valid b))) step12CommonPoint19 = true)
def step12CommonGroup19 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope19 step12CommonScope19_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint19
  (fun a => step12CommonGroup19_sources a 0) (fun b => step12CommonGroup19_neighbors b 0)

def step12CommonScope20 : Scope := ⟨18, 6, 9, 1⟩
theorem step12CommonScope20_valid : step12CommonScope20.Valid 49 12 := by decide +kernel

def step12CommonPoint20 : CommonPoint.Point := ⟨2517, 1859, 1000⟩
kernel_matrix step12CommonGroup20_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope20.sourceIndex step12CommonScope20_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope20.sourceIndex step12CommonScope20_valid a))) step12CommonPoint20 = true)
kernel_matrix step12CommonGroup20_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope20.neighborIndex step12CommonScope20_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope20.neighborIndex step12CommonScope20_valid b))) step12CommonPoint20 = true)
def step12CommonGroup20 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope20 step12CommonScope20_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint20
  (fun a => step12CommonGroup20_sources a 0) (fun b => step12CommonGroup20_neighbors b 0)

def step12CommonScope21 : Scope := ⟨18, 6, 10, 1⟩
theorem step12CommonScope21_valid : step12CommonScope21.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup21_checked : 6 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope21.sourceIndex step12CommonScope21_valid a))
    (step12CommonRawNeighbors (step12CommonScope21.neighborIndex step12CommonScope21_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope21.sourceIndex step12CommonScope21_valid a))
      (step12CommonNeighborAngles (step12CommonScope21.neighborIndex step12CommonScope21_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup21 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope21 step12CommonScope21_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup21_checked

def step12CommonScope22 : Scope := ⟨18, 6, 11, 1⟩
theorem step12CommonScope22_valid : step12CommonScope22.Valid 49 12 := by decide +kernel

def step12CommonPoint22 : CommonPoint.Point := ⟨2363, 2016, 1000⟩
kernel_matrix step12CommonGroup22_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope22.sourceIndex step12CommonScope22_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope22.sourceIndex step12CommonScope22_valid a))) step12CommonPoint22 = true)
kernel_matrix step12CommonGroup22_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope22.neighborIndex step12CommonScope22_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope22.neighborIndex step12CommonScope22_valid b))) step12CommonPoint22 = true)
def step12CommonGroup22 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope22 step12CommonScope22_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint22
  (fun a => step12CommonGroup22_sources a 0) (fun b => step12CommonGroup22_neighbors b 0)

def step12CommonScope23 : Scope := ⟨24, 6, 0, 1⟩
theorem step12CommonScope23_valid : step12CommonScope23.Valid 49 12 := by decide +kernel

def step12CommonPoint23 : CommonPoint.Point := ⟨118562651, 100359927, 50000000⟩
kernel_matrix step12CommonGroup23_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope23.sourceIndex step12CommonScope23_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope23.sourceIndex step12CommonScope23_valid a))) step12CommonPoint23 = true)
kernel_matrix step12CommonGroup23_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope23.neighborIndex step12CommonScope23_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope23.neighborIndex step12CommonScope23_valid b))) step12CommonPoint23 = true)
def step12CommonGroup23 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope23 step12CommonScope23_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint23
  (fun a => step12CommonGroup23_sources a 0) (fun b => step12CommonGroup23_neighbors b 0)

def step12CommonScope24 : Scope := ⟨24, 6, 1, 1⟩
theorem step12CommonScope24_valid : step12CommonScope24.Valid 49 12 := by decide +kernel

def step12CommonPoint24 : CommonPoint.Point := ⟨2384, 1993, 1000⟩
kernel_matrix step12CommonGroup24_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope24.sourceIndex step12CommonScope24_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope24.sourceIndex step12CommonScope24_valid a))) step12CommonPoint24 = true)
kernel_matrix step12CommonGroup24_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope24.neighborIndex step12CommonScope24_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope24.neighborIndex step12CommonScope24_valid b))) step12CommonPoint24 = true)
def step12CommonGroup24 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope24 step12CommonScope24_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint24
  (fun a => step12CommonGroup24_sources a 0) (fun b => step12CommonGroup24_neighbors b 0)

def step12CommonScope25 : Scope := ⟨24, 6, 2, 1⟩
theorem step12CommonScope25_valid : step12CommonScope25.Valid 49 12 := by decide +kernel

def step12CommonPoint25 : CommonPoint.Point := ⟨1199, 989, 500⟩
kernel_matrix step12CommonGroup25_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope25.sourceIndex step12CommonScope25_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope25.sourceIndex step12CommonScope25_valid a))) step12CommonPoint25 = true)
kernel_matrix step12CommonGroup25_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope25.neighborIndex step12CommonScope25_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope25.neighborIndex step12CommonScope25_valid b))) step12CommonPoint25 = true)
def step12CommonGroup25 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope25 step12CommonScope25_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint25
  (fun a => step12CommonGroup25_sources a 0) (fun b => step12CommonGroup25_neighbors b 0)

def step12CommonScope26 : Scope := ⟨24, 6, 3, 1⟩
theorem step12CommonScope26_valid : step12CommonScope26.Valid 49 12 := by decide +kernel

def step12CommonPoint26 : CommonPoint.Point := ⟨1206, 981, 500⟩
kernel_matrix step12CommonGroup26_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope26.sourceIndex step12CommonScope26_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope26.sourceIndex step12CommonScope26_valid a))) step12CommonPoint26 = true)
kernel_matrix step12CommonGroup26_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope26.neighborIndex step12CommonScope26_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope26.neighborIndex step12CommonScope26_valid b))) step12CommonPoint26 = true)
def step12CommonGroup26 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope26 step12CommonScope26_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint26
  (fun a => step12CommonGroup26_sources a 0) (fun b => step12CommonGroup26_neighbors b 0)

def step12CommonScope27 : Scope := ⟨24, 6, 4, 1⟩
theorem step12CommonScope27_valid : step12CommonScope27.Valid 49 12 := by decide +kernel

def step12CommonPoint27 : CommonPoint.Point := ⟨2427, 1947, 1000⟩
kernel_matrix step12CommonGroup27_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope27.sourceIndex step12CommonScope27_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope27.sourceIndex step12CommonScope27_valid a))) step12CommonPoint27 = true)
kernel_matrix step12CommonGroup27_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope27.neighborIndex step12CommonScope27_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope27.neighborIndex step12CommonScope27_valid b))) step12CommonPoint27 = true)
def step12CommonGroup27 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope27 step12CommonScope27_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint27
  (fun a => step12CommonGroup27_sources a 0) (fun b => step12CommonGroup27_neighbors b 0)

def step12CommonScope28 : Scope := ⟨24, 6, 5, 1⟩
theorem step12CommonScope28_valid : step12CommonScope28.Valid 49 12 := by decide +kernel

def step12CommonPoint28 : CommonPoint.Point := ⟨2443, 1931, 1000⟩
kernel_matrix step12CommonGroup28_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope28.sourceIndex step12CommonScope28_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope28.sourceIndex step12CommonScope28_valid a))) step12CommonPoint28 = true)
kernel_matrix step12CommonGroup28_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope28.neighborIndex step12CommonScope28_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope28.neighborIndex step12CommonScope28_valid b))) step12CommonPoint28 = true)
def step12CommonGroup28 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope28 step12CommonScope28_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint28
  (fun a => step12CommonGroup28_sources a 0) (fun b => step12CommonGroup28_neighbors b 0)

def step12CommonScope29 : Scope := ⟨30, 3, 0, 3⟩
theorem step12CommonScope29_valid : step12CommonScope29.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup29_checked : 3 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope29.sourceIndex step12CommonScope29_valid a))
    (step12CommonRawNeighbors (step12CommonScope29.neighborIndex step12CommonScope29_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope29.sourceIndex step12CommonScope29_valid a))
      (step12CommonNeighborAngles (step12CommonScope29.neighborIndex step12CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup29 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope29 step12CommonScope29_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup29_checked

def step12CommonScope30 : Scope := ⟨33, 3, 0, 3⟩
theorem step12CommonScope30_valid : step12CommonScope30.Valid 49 12 := by decide +kernel

def step12CommonPoint30 : CommonPoint.Point := ⟨1215, 1017, 500⟩
kernel_matrix step12CommonGroup30_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope30.sourceIndex step12CommonScope30_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope30.sourceIndex step12CommonScope30_valid a))) step12CommonPoint30 = true)
kernel_matrix step12CommonGroup30_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope30.neighborIndex step12CommonScope30_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope30.neighborIndex step12CommonScope30_valid b))) step12CommonPoint30 = true)
def step12CommonGroup30 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope30 step12CommonScope30_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint30
  (fun a => step12CommonGroup30_sources a 0) (fun b => step12CommonGroup30_neighbors b 0)

def step12CommonScope31 : Scope := ⟨30, 6, 3, 3⟩
theorem step12CommonScope31_valid : step12CommonScope31.Valid 49 12 := by decide +kernel

def step12CommonPoint31 : CommonPoint.Point := ⟨2434, 1961, 1000⟩
kernel_matrix step12CommonGroup31_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope31.sourceIndex step12CommonScope31_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope31.sourceIndex step12CommonScope31_valid a))) step12CommonPoint31 = true)
kernel_matrix step12CommonGroup31_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope31.neighborIndex step12CommonScope31_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope31.neighborIndex step12CommonScope31_valid b))) step12CommonPoint31 = true)
def step12CommonGroup31 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope31 step12CommonScope31_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint31
  (fun a => step12CommonGroup31_sources a 0) (fun b => step12CommonGroup31_neighbors b 0)

def step12CommonScope32 : Scope := ⟨24, 6, 6, 1⟩
theorem step12CommonScope32_valid : step12CommonScope32.Valid 49 12 := by decide +kernel

def step12CommonPoint32 : CommonPoint.Point := ⟨2459, 1914, 1000⟩
kernel_matrix step12CommonGroup32_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope32.sourceIndex step12CommonScope32_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope32.sourceIndex step12CommonScope32_valid a))) step12CommonPoint32 = true)
kernel_matrix step12CommonGroup32_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope32.neighborIndex step12CommonScope32_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope32.neighborIndex step12CommonScope32_valid b))) step12CommonPoint32 = true)
def step12CommonGroup32 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope32 step12CommonScope32_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint32
  (fun a => step12CommonGroup32_sources a 0) (fun b => step12CommonGroup32_neighbors b 0)

def step12CommonScope33 : Scope := ⟨24, 6, 7, 1⟩
theorem step12CommonScope33_valid : step12CommonScope33.Valid 49 12 := by decide +kernel

def step12CommonPoint33 : CommonPoint.Point := ⟨2477, 1897, 1000⟩
kernel_matrix step12CommonGroup33_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope33.sourceIndex step12CommonScope33_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope33.sourceIndex step12CommonScope33_valid a))) step12CommonPoint33 = true)
kernel_matrix step12CommonGroup33_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope33.neighborIndex step12CommonScope33_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope33.neighborIndex step12CommonScope33_valid b))) step12CommonPoint33 = true)
def step12CommonGroup33 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope33 step12CommonScope33_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint33
  (fun a => step12CommonGroup33_sources a 0) (fun b => step12CommonGroup33_neighbors b 0)

def step12CommonScope34 : Scope := ⟨24, 6, 8, 1⟩
theorem step12CommonScope34_valid : step12CommonScope34.Valid 49 12 := by decide +kernel

def step12CommonPoint34 : CommonPoint.Point := ⟨2496, 1879, 1000⟩
kernel_matrix step12CommonGroup34_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope34.sourceIndex step12CommonScope34_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope34.sourceIndex step12CommonScope34_valid a))) step12CommonPoint34 = true)
kernel_matrix step12CommonGroup34_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope34.neighborIndex step12CommonScope34_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope34.neighborIndex step12CommonScope34_valid b))) step12CommonPoint34 = true)
def step12CommonGroup34 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope34 step12CommonScope34_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint34
  (fun a => step12CommonGroup34_sources a 0) (fun b => step12CommonGroup34_neighbors b 0)

def step12CommonScope35 : Scope := ⟨24, 6, 9, 1⟩
theorem step12CommonScope35_valid : step12CommonScope35.Valid 49 12 := by decide +kernel

def step12CommonPoint35 : CommonPoint.Point := ⟨2517, 1859, 1000⟩
kernel_matrix step12CommonGroup35_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope35.sourceIndex step12CommonScope35_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope35.sourceIndex step12CommonScope35_valid a))) step12CommonPoint35 = true)
kernel_matrix step12CommonGroup35_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope35.neighborIndex step12CommonScope35_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope35.neighborIndex step12CommonScope35_valid b))) step12CommonPoint35 = true)
def step12CommonGroup35 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope35 step12CommonScope35_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint35
  (fun a => step12CommonGroup35_sources a 0) (fun b => step12CommonGroup35_neighbors b 0)

def step12CommonScope36 : Scope := ⟨24, 6, 10, 1⟩
theorem step12CommonScope36_valid : step12CommonScope36.Valid 49 12 := by decide +kernel

def step12CommonPoint36 : CommonPoint.Point := ⟨25393, 18385, 10000⟩
kernel_matrix step12CommonGroup36_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope36.sourceIndex step12CommonScope36_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope36.sourceIndex step12CommonScope36_valid a))) step12CommonPoint36 = true)
kernel_matrix step12CommonGroup36_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope36.neighborIndex step12CommonScope36_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope36.neighborIndex step12CommonScope36_valid b))) step12CommonPoint36 = true)
def step12CommonGroup36 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope36 step12CommonScope36_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint36
  (fun a => step12CommonGroup36_sources a 0) (fun b => step12CommonGroup36_neighbors b 0)

def step12CommonScope37 : Scope := ⟨24, 6, 11, 1⟩
theorem step12CommonScope37_valid : step12CommonScope37.Valid 49 12 := by decide +kernel

def step12CommonPoint37 : CommonPoint.Point := ⟨590, 503, 250⟩
kernel_matrix step12CommonGroup37_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope37.sourceIndex step12CommonScope37_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope37.sourceIndex step12CommonScope37_valid a))) step12CommonPoint37 = true)
kernel_matrix step12CommonGroup37_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope37.neighborIndex step12CommonScope37_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope37.neighborIndex step12CommonScope37_valid b))) step12CommonPoint37 = true)
def step12CommonGroup37 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope37 step12CommonScope37_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint37
  (fun a => step12CommonGroup37_sources a 0) (fun b => step12CommonGroup37_neighbors b 0)

def step12CommonScope38 : Scope := ⟨30, 6, 6, 3⟩
theorem step12CommonScope38_valid : step12CommonScope38.Valid 49 12 := by decide +kernel

def step12CommonPoint38 : CommonPoint.Point := ⟨2487, 1919, 1000⟩
kernel_matrix step12CommonGroup38_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope38.sourceIndex step12CommonScope38_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope38.sourceIndex step12CommonScope38_valid a))) step12CommonPoint38 = true)
kernel_matrix step12CommonGroup38_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope38.neighborIndex step12CommonScope38_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope38.neighborIndex step12CommonScope38_valid b))) step12CommonPoint38 = true)
def step12CommonGroup38 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope38 step12CommonScope38_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint38
  (fun a => step12CommonGroup38_sources a 0) (fun b => step12CommonGroup38_neighbors b 0)

def step12CommonScope39 : Scope := ⟨30, 3, 9, 1⟩
theorem step12CommonScope39_valid : step12CommonScope39.Valid 49 12 := by decide +kernel

def step12CommonPoint39 : CommonPoint.Point := ⟨505, 376, 200⟩
kernel_matrix step12CommonGroup39_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope39.sourceIndex step12CommonScope39_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope39.sourceIndex step12CommonScope39_valid a))) step12CommonPoint39 = true)
kernel_matrix step12CommonGroup39_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope39.neighborIndex step12CommonScope39_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope39.neighborIndex step12CommonScope39_valid b))) step12CommonPoint39 = true)
def step12CommonGroup39 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope39 step12CommonScope39_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint39
  (fun a => step12CommonGroup39_sources a 0) (fun b => step12CommonGroup39_neighbors b 0)

def step12CommonScope40 : Scope := ⟨30, 3, 10, 2⟩
theorem step12CommonScope40_valid : step12CommonScope40.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup40_checked : 3 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope40.sourceIndex step12CommonScope40_valid a))
    (step12CommonRawNeighbors (step12CommonScope40.neighborIndex step12CommonScope40_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope40.sourceIndex step12CommonScope40_valid a))
      (step12CommonNeighborAngles (step12CommonScope40.neighborIndex step12CommonScope40_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup40 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope40 step12CommonScope40_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup40_checked

def step12CommonScope41 : Scope := ⟨33, 3, 9, 3⟩
theorem step12CommonScope41_valid : step12CommonScope41.Valid 49 12 := by decide +kernel

def step12CommonPoint41 : CommonPoint.Point := ⟨2489, 2016, 1000⟩
kernel_matrix step12CommonGroup41_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope41.sourceIndex step12CommonScope41_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope41.sourceIndex step12CommonScope41_valid a))) step12CommonPoint41 = true)
kernel_matrix step12CommonGroup41_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope41.neighborIndex step12CommonScope41_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope41.neighborIndex step12CommonScope41_valid b))) step12CommonPoint41 = true)
def step12CommonGroup41 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope41 step12CommonScope41_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint41
  (fun a => step12CommonGroup41_sources a 0) (fun b => step12CommonGroup41_neighbors b 0)

def step12CommonScope42 : Scope := ⟨36, 6, 0, 3⟩
theorem step12CommonScope42_valid : step12CommonScope42.Valid 49 12 := by decide +kernel

def step12CommonPoint42 : CommonPoint.Point := ⟨2400, 2011, 1000⟩
kernel_matrix step12CommonGroup42_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope42.sourceIndex step12CommonScope42_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope42.sourceIndex step12CommonScope42_valid a))) step12CommonPoint42 = true)
kernel_matrix step12CommonGroup42_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope42.neighborIndex step12CommonScope42_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope42.neighborIndex step12CommonScope42_valid b))) step12CommonPoint42 = true)
def step12CommonGroup42 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope42 step12CommonScope42_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint42
  (fun a => step12CommonGroup42_sources a 0) (fun b => step12CommonGroup42_neighbors b 0)

def step12CommonScope43 : Scope := ⟨36, 6, 3, 3⟩
theorem step12CommonScope43_valid : step12CommonScope43.Valid 49 12 := by decide +kernel

def step12CommonPoint43 : CommonPoint.Point := ⟨2456, 1977, 1000⟩
kernel_matrix step12CommonGroup43_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope43.sourceIndex step12CommonScope43_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope43.sourceIndex step12CommonScope43_valid a))) step12CommonPoint43 = true)
kernel_matrix step12CommonGroup43_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope43.neighborIndex step12CommonScope43_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope43.neighborIndex step12CommonScope43_valid b))) step12CommonPoint43 = true)
def step12CommonGroup43 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope43 step12CommonScope43_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint43
  (fun a => step12CommonGroup43_sources a 0) (fun b => step12CommonGroup43_neighbors b 0)

def step12CommonScope44 : Scope := ⟨36, 6, 6, 3⟩
theorem step12CommonScope44_valid : step12CommonScope44.Valid 49 12 := by decide +kernel

def step12CommonPoint44 : CommonPoint.Point := ⟨2513, 1945, 1000⟩
kernel_matrix step12CommonGroup44_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope44.sourceIndex step12CommonScope44_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope44.sourceIndex step12CommonScope44_valid a))) step12CommonPoint44 = true)
kernel_matrix step12CommonGroup44_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope44.neighborIndex step12CommonScope44_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope44.neighborIndex step12CommonScope44_valid b))) step12CommonPoint44 = true)
def step12CommonGroup44 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope44 step12CommonScope44_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint44
  (fun a => step12CommonGroup44_sources a 0) (fun b => step12CommonGroup44_neighbors b 0)

def step12CommonScope45 : Scope := ⟨36, 6, 9, 1⟩
theorem step12CommonScope45_valid : step12CommonScope45.Valid 49 12 := by decide +kernel

def step12CommonPoint45 : CommonPoint.Point := ⟨2577, 1912, 1000⟩
kernel_matrix step12CommonGroup45_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope45.sourceIndex step12CommonScope45_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope45.sourceIndex step12CommonScope45_valid a))) step12CommonPoint45 = true)
kernel_matrix step12CommonGroup45_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope45.neighborIndex step12CommonScope45_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope45.neighborIndex step12CommonScope45_valid b))) step12CommonPoint45 = true)
def step12CommonGroup45 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope45 step12CommonScope45_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint45
  (fun a => step12CommonGroup45_sources a 0) (fun b => step12CommonGroup45_neighbors b 0)

def step12CommonScope46 : Scope := ⟨36, 6, 10, 1⟩
theorem step12CommonScope46_valid : step12CommonScope46.Valid 49 12 := by decide +kernel

def step12CommonPoint46 : CommonPoint.Point := ⟨2621, 1901, 1000⟩
kernel_matrix step12CommonGroup46_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope46.sourceIndex step12CommonScope46_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope46.sourceIndex step12CommonScope46_valid a))) step12CommonPoint46 = true)
kernel_matrix step12CommonGroup46_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope46.neighborIndex step12CommonScope46_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope46.neighborIndex step12CommonScope46_valid b))) step12CommonPoint46 = true)
def step12CommonGroup46 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope46 step12CommonScope46_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint46
  (fun a => step12CommonGroup46_sources a 0) (fun b => step12CommonGroup46_neighbors b 0)

def step12CommonScope47 : Scope := ⟨36, 6, 11, 1⟩
theorem step12CommonScope47_valid : step12CommonScope47.Valid 49 12 := by decide +kernel

def step12CommonPoint47 : CommonPoint.Point := ⟨2375, 2017, 1000⟩
kernel_matrix step12CommonGroup47_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope47.sourceIndex step12CommonScope47_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope47.sourceIndex step12CommonScope47_valid a))) step12CommonPoint47 = true)
kernel_matrix step12CommonGroup47_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope47.neighborIndex step12CommonScope47_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope47.neighborIndex step12CommonScope47_valid b))) step12CommonPoint47 = true)
def step12CommonGroup47 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope47 step12CommonScope47_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint47
  (fun a => step12CommonGroup47_sources a 0) (fun b => step12CommonGroup47_neighbors b 0)

def step12CommonScope48 : Scope := ⟨42, 7, 0, 6⟩
theorem step12CommonScope48_valid : step12CommonScope48.Valid 49 12 := by decide +kernel

def step12CommonPoint48 : CommonPoint.Point := ⟨2431, 2010, 1000⟩
kernel_matrix step12CommonGroup48_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope48.sourceIndex step12CommonScope48_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope48.sourceIndex step12CommonScope48_valid a))) step12CommonPoint48 = true)
kernel_matrix step12CommonGroup48_neighbors : 6 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope48.neighborIndex step12CommonScope48_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope48.neighborIndex step12CommonScope48_valid b))) step12CommonPoint48 = true)
def step12CommonGroup48 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope48 step12CommonScope48_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint48
  (fun a => step12CommonGroup48_sources a 0) (fun b => step12CommonGroup48_neighbors b 0)

def step12CommonScope49 : Scope := ⟨42, 7, 6, 3⟩
theorem step12CommonScope49_valid : step12CommonScope49.Valid 49 12 := by decide +kernel

def step12CommonPoint49 : CommonPoint.Point := ⟨2595, 1957, 1000⟩
kernel_matrix step12CommonGroup49_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope49.sourceIndex step12CommonScope49_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope49.sourceIndex step12CommonScope49_valid a))) step12CommonPoint49 = true)
kernel_matrix step12CommonGroup49_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope49.neighborIndex step12CommonScope49_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope49.neighborIndex step12CommonScope49_valid b))) step12CommonPoint49 = true)
def step12CommonGroup49 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope49 step12CommonScope49_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint49
  (fun a => step12CommonGroup49_sources a 0) (fun b => step12CommonGroup49_neighbors b 0)

def step12CommonScope50 : Scope := ⟨42, 3, 9, 3⟩
theorem step12CommonScope50_valid : step12CommonScope50.Valid 49 12 := by decide +kernel

def step12CommonPoint50 : CommonPoint.Point := ⟨1244, 1005, 500⟩
kernel_matrix step12CommonGroup50_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope50.sourceIndex step12CommonScope50_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope50.sourceIndex step12CommonScope50_valid a))) step12CommonPoint50 = true)
kernel_matrix step12CommonGroup50_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope50.neighborIndex step12CommonScope50_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope50.neighborIndex step12CommonScope50_valid b))) step12CommonPoint50 = true)
def step12CommonGroup50 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope50 step12CommonScope50_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint50
  (fun a => step12CommonGroup50_sources a 0) (fun b => step12CommonGroup50_neighbors b 0)

def step12CommonScope51 : Scope := ⟨45, 4, 9, 1⟩
theorem step12CommonScope51_valid : step12CommonScope51.Valid 49 12 := by decide +kernel

def step12CommonPoint51 : CommonPoint.Point := ⟨2632, 1941, 1000⟩
kernel_matrix step12CommonGroup51_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step12CommonRawSources (step12CommonScope51.sourceIndex step12CommonScope51_valid a))
    (ownKeys (step12CommonSourceAngles (step12CommonScope51.sourceIndex step12CommonScope51_valid a))) step12CommonPoint51 = true)
kernel_matrix step12CommonGroup51_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step12CommonRawNeighbors (step12CommonScope51.neighborIndex step12CommonScope51_valid b))
    (ownKeys (step12CommonNeighborAngles (step12CommonScope51.neighborIndex step12CommonScope51_valid b))) step12CommonPoint51 = true)
def step12CommonGroup51 : CheckedGroup step12Sources step12Neighbors := pointGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope51 step12CommonScope51_valid
  (fun i => ownKeys (step12CommonSourceAngles i))
  (fun j => ownKeys (step12CommonNeighborAngles j)) step12CommonPoint51
  (fun a => step12CommonGroup51_sources a 0) (fun b => step12CommonGroup51_neighbors b 0)

def step12CommonScope52 : Scope := ⟨45, 4, 10, 2⟩
theorem step12CommonScope52_valid : step12CommonScope52.Valid 49 12 := by decide +kernel

kernel_matrix step12CommonGroup52_checked : 4 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step12CommonRawSources (step12CommonScope52.sourceIndex step12CommonScope52_valid a))
    (step12CommonRawNeighbors (step12CommonScope52.neighborIndex step12CommonScope52_valid b))
    (fanDirectionKey (step12CommonSourceAngles (step12CommonScope52.sourceIndex step12CommonScope52_valid a))
      (step12CommonNeighborAngles (step12CommonScope52.neighborIndex step12CommonScope52_valid b))) (fun key => (key + 128) % 256))
def step12CommonGroup52 : CheckedGroup step12Sources step12Neighbors := fallbackGroup
  step12Sources step12Neighbors
  step12CommonRawSources step12CommonRawNeighbors
  step12CommonRawSources_exact step12CommonRawNeighbors_exact
  step12CommonNeighborUnblocked step12CommonScope52 step12CommonScope52_valid
  step12CommonSourceAngles step12CommonNeighborAngles
  step12CommonSourceAngles_exact step12CommonNeighborAngles_exact
  step12CommonGroup52_checked

def step12CommonScopes : List Scope := [
  step12CommonScope0, step12CommonScope1, step12CommonScope2, step12CommonScope3, step12CommonScope4, step12CommonScope5, step12CommonScope6, step12CommonScope7, step12CommonScope8, step12CommonScope9, step12CommonScope10, step12CommonScope11, step12CommonScope12, step12CommonScope13, step12CommonScope14, step12CommonScope15, step12CommonScope16, step12CommonScope17, step12CommonScope18, step12CommonScope19, step12CommonScope20, step12CommonScope21, step12CommonScope22, step12CommonScope23, step12CommonScope24, step12CommonScope25, step12CommonScope26, step12CommonScope27, step12CommonScope28, step12CommonScope29, step12CommonScope30, step12CommonScope31, step12CommonScope32, step12CommonScope33, step12CommonScope34, step12CommonScope35, step12CommonScope36, step12CommonScope37, step12CommonScope38, step12CommonScope39, step12CommonScope40, step12CommonScope41, step12CommonScope42, step12CommonScope43, step12CommonScope44, step12CommonScope45, step12CommonScope46, step12CommonScope47, step12CommonScope48, step12CommonScope49, step12CommonScope50, step12CommonScope51, step12CommonScope52]
def step12CommonGroups : List (CheckedGroup step12Sources step12Neighbors) := [
  step12CommonGroup0, step12CommonGroup1, step12CommonGroup2, step12CommonGroup3, step12CommonGroup4, step12CommonGroup5, step12CommonGroup6, step12CommonGroup7, step12CommonGroup8, step12CommonGroup9, step12CommonGroup10, step12CommonGroup11, step12CommonGroup12, step12CommonGroup13, step12CommonGroup14, step12CommonGroup15, step12CommonGroup16, step12CommonGroup17, step12CommonGroup18, step12CommonGroup19, step12CommonGroup20, step12CommonGroup21, step12CommonGroup22, step12CommonGroup23, step12CommonGroup24, step12CommonGroup25, step12CommonGroup26, step12CommonGroup27, step12CommonGroup28, step12CommonGroup29, step12CommonGroup30, step12CommonGroup31, step12CommonGroup32, step12CommonGroup33, step12CommonGroup34, step12CommonGroup35, step12CommonGroup36, step12CommonGroup37, step12CommonGroup38, step12CommonGroup39, step12CommonGroup40, step12CommonGroup41, step12CommonGroup42, step12CommonGroup43, step12CommonGroup44, step12CommonGroup45, step12CommonGroup46, step12CommonGroup47, step12CommonGroup48, step12CommonGroup49, step12CommonGroup50, step12CommonGroup51, step12CommonGroup52]
theorem step12CommonScopes_exact :
    step12CommonGroups.map CheckedGroup.scope = step12CommonScopes := rfl
kernel_matrix step12CommonCoverage : 49 × 12 => (fun i j =>
  ScopeCheck step12CommonScopes i.val j.val)
theorem step12_geometric_overlap (i : Fin 49) (j : Fin 12) :
    PairOverlaps (step12Sources i) (step12Neighbors j) :=
  groups_sound step12Sources step12Neighbors step12CommonGroups
    step12CommonScopes step12CommonScopes_exact step12CommonCoverage i j
#print axioms step12_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
