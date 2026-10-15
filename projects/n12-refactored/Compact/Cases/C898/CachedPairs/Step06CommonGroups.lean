import Compact.Cases.C898.CachedPairs.Step06CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step6CommonScope0 : Scope := ⟨0, 14, 0, 14⟩
theorem step6CommonScope0_valid : step6CommonScope0.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup0_checked : 14 × 14 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope0.sourceIndex step6CommonScope0_valid a))
    (step6CommonRawNeighbors (step6CommonScope0.neighborIndex step6CommonScope0_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope0.sourceIndex step6CommonScope0_valid a))
      (step6CommonNeighborAngles (step6CommonScope0.neighborIndex step6CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup0 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope0 step6CommonScope0_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup0_checked

def step6CommonScope1 : Scope := ⟨14, 7, 0, 14⟩
theorem step6CommonScope1_valid : step6CommonScope1.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup1_checked : 7 × 14 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope1.sourceIndex step6CommonScope1_valid a))
    (step6CommonRawNeighbors (step6CommonScope1.neighborIndex step6CommonScope1_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope1.sourceIndex step6CommonScope1_valid a))
      (step6CommonNeighborAngles (step6CommonScope1.neighborIndex step6CommonScope1_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup1 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope1 step6CommonScope1_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup1_checked

def step6CommonScope2 : Scope := ⟨21, 8, 0, 7⟩
theorem step6CommonScope2_valid : step6CommonScope2.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup2_checked : 8 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope2.sourceIndex step6CommonScope2_valid a))
    (step6CommonRawNeighbors (step6CommonScope2.neighborIndex step6CommonScope2_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope2.sourceIndex step6CommonScope2_valid a))
      (step6CommonNeighborAngles (step6CommonScope2.neighborIndex step6CommonScope2_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup2 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope2 step6CommonScope2_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup2_checked

def step6CommonScope3 : Scope := ⟨21, 4, 7, 7⟩
theorem step6CommonScope3_valid : step6CommonScope3.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup3_checked : 4 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope3.sourceIndex step6CommonScope3_valid a))
    (step6CommonRawNeighbors (step6CommonScope3.neighborIndex step6CommonScope3_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope3.sourceIndex step6CommonScope3_valid a))
      (step6CommonNeighborAngles (step6CommonScope3.neighborIndex step6CommonScope3_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup3 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope3 step6CommonScope3_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup3_checked

def step6CommonScope4 : Scope := ⟨25, 4, 7, 7⟩
theorem step6CommonScope4_valid : step6CommonScope4.Valid 59 59 := by decide +kernel

def step6CommonPoint4 : CommonPoint.Point := ⟨1610, 2947, 1000⟩
kernel_matrix step6CommonGroup4_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope4.sourceIndex step6CommonScope4_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope4.sourceIndex step6CommonScope4_valid a))) step6CommonPoint4 = true)
kernel_matrix step6CommonGroup4_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope4.neighborIndex step6CommonScope4_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope4.neighborIndex step6CommonScope4_valid b))) step6CommonPoint4 = true)
def step6CommonGroup4 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope4 step6CommonScope4_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint4
  (fun a => step6CommonGroup4_sources a 0) (fun b => step6CommonGroup4_neighbors b 0)

def step6CommonScope5 : Scope := ⟨0, 14, 14, 3⟩
theorem step6CommonScope5_valid : step6CommonScope5.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup5_checked : 14 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope5.sourceIndex step6CommonScope5_valid a))
    (step6CommonRawNeighbors (step6CommonScope5.neighborIndex step6CommonScope5_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope5.sourceIndex step6CommonScope5_valid a))
      (step6CommonNeighborAngles (step6CommonScope5.neighborIndex step6CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup5 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope5 step6CommonScope5_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup5_checked

def step6CommonScope6 : Scope := ⟨0, 14, 17, 4⟩
theorem step6CommonScope6_valid : step6CommonScope6.Valid 59 59 := by decide +kernel

def step6CommonPoint6 : CommonPoint.Point := ⟨756, 1403, 500⟩
kernel_matrix step6CommonGroup6_sources : 14 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope6.sourceIndex step6CommonScope6_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope6.sourceIndex step6CommonScope6_valid a))) step6CommonPoint6 = true)
kernel_matrix step6CommonGroup6_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope6.neighborIndex step6CommonScope6_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope6.neighborIndex step6CommonScope6_valid b))) step6CommonPoint6 = true)
def step6CommonGroup6 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope6 step6CommonScope6_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint6
  (fun a => step6CommonGroup6_sources a 0) (fun b => step6CommonGroup6_neighbors b 0)

def step6CommonScope7 : Scope := ⟨14, 7, 14, 7⟩
theorem step6CommonScope7_valid : step6CommonScope7.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup7_checked : 7 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope7.sourceIndex step6CommonScope7_valid a))
    (step6CommonRawNeighbors (step6CommonScope7.neighborIndex step6CommonScope7_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope7.sourceIndex step6CommonScope7_valid a))
      (step6CommonNeighborAngles (step6CommonScope7.neighborIndex step6CommonScope7_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup7 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope7 step6CommonScope7_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup7_checked

def step6CommonScope8 : Scope := ⟨21, 8, 14, 7⟩
theorem step6CommonScope8_valid : step6CommonScope8.Valid 59 59 := by decide +kernel

def step6CommonPoint8 : CommonPoint.Point := ⟨1643, 2903, 1000⟩
kernel_matrix step6CommonGroup8_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope8.sourceIndex step6CommonScope8_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope8.sourceIndex step6CommonScope8_valid a))) step6CommonPoint8 = true)
kernel_matrix step6CommonGroup8_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope8.neighborIndex step6CommonScope8_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope8.neighborIndex step6CommonScope8_valid b))) step6CommonPoint8 = true)
def step6CommonGroup8 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope8 step6CommonScope8_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint8
  (fun a => step6CommonGroup8_sources a 0) (fun b => step6CommonGroup8_neighbors b 0)

def step6CommonScope9 : Scope := ⟨0, 29, 21, 8⟩
theorem step6CommonScope9_valid : step6CommonScope9.Valid 59 59 := by decide +kernel

def step6CommonPoint9 : CommonPoint.Point := ⟨1598, 2815, 1000⟩
kernel_matrix step6CommonGroup9_sources : 29 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope9.sourceIndex step6CommonScope9_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope9.sourceIndex step6CommonScope9_valid a))) step6CommonPoint9 = true)
kernel_matrix step6CommonGroup9_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope9.neighborIndex step6CommonScope9_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope9.neighborIndex step6CommonScope9_valid b))) step6CommonPoint9 = true)
def step6CommonGroup9 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope9 step6CommonScope9_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint9
  (fun a => step6CommonGroup9_sources a 0) (fun b => step6CommonGroup9_neighbors b 0)

def step6CommonScope10 : Scope := ⟨29, 15, 0, 7⟩
theorem step6CommonScope10_valid : step6CommonScope10.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup10_checked : 15 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope10.sourceIndex step6CommonScope10_valid a))
    (step6CommonRawNeighbors (step6CommonScope10.neighborIndex step6CommonScope10_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope10.sourceIndex step6CommonScope10_valid a))
      (step6CommonNeighborAngles (step6CommonScope10.neighborIndex step6CommonScope10_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup10 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope10 step6CommonScope10_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup10_checked

def step6CommonScope11 : Scope := ⟨44, 15, 0, 3⟩
theorem step6CommonScope11_valid : step6CommonScope11.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup11_checked : 15 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope11.sourceIndex step6CommonScope11_valid a))
    (step6CommonRawNeighbors (step6CommonScope11.neighborIndex step6CommonScope11_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope11.sourceIndex step6CommonScope11_valid a))
      (step6CommonNeighborAngles (step6CommonScope11.neighborIndex step6CommonScope11_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup11 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope11 step6CommonScope11_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup11_checked

def step6CommonScope12 : Scope := ⟨44, 15, 3, 4⟩
theorem step6CommonScope12_valid : step6CommonScope12.Valid 59 59 := by decide +kernel

def step6CommonPoint12 : CommonPoint.Point := ⟨698, 1477, 500⟩
kernel_matrix step6CommonGroup12_sources : 15 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope12.sourceIndex step6CommonScope12_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope12.sourceIndex step6CommonScope12_valid a))) step6CommonPoint12 = true)
kernel_matrix step6CommonGroup12_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope12.neighborIndex step6CommonScope12_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope12.neighborIndex step6CommonScope12_valid b))) step6CommonPoint12 = true)
def step6CommonGroup12 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope12 step6CommonScope12_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint12
  (fun a => step6CommonGroup12_sources a 0) (fun b => step6CommonGroup12_neighbors b 0)

def step6CommonScope13 : Scope := ⟨29, 30, 7, 7⟩
theorem step6CommonScope13_valid : step6CommonScope13.Valid 59 59 := by decide +kernel

def step6CommonPoint13 : CommonPoint.Point := ⟨1498, 2919, 1000⟩
kernel_matrix step6CommonGroup13_sources : 30 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope13.sourceIndex step6CommonScope13_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope13.sourceIndex step6CommonScope13_valid a))) step6CommonPoint13 = true)
kernel_matrix step6CommonGroup13_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope13.neighborIndex step6CommonScope13_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope13.neighborIndex step6CommonScope13_valid b))) step6CommonPoint13 = true)
def step6CommonGroup13 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope13 step6CommonScope13_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint13
  (fun a => step6CommonGroup13_sources a 0) (fun b => step6CommonGroup13_neighbors b 0)

def step6CommonScope14 : Scope := ⟨29, 30, 14, 15⟩
theorem step6CommonScope14_valid : step6CommonScope14.Valid 59 59 := by decide +kernel

def step6CommonPoint14 : CommonPoint.Point := ⟨38, 72, 25⟩
kernel_matrix step6CommonGroup14_sources : 30 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope14.sourceIndex step6CommonScope14_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope14.sourceIndex step6CommonScope14_valid a))) step6CommonPoint14 = true)
kernel_matrix step6CommonGroup14_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope14.neighborIndex step6CommonScope14_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope14.neighborIndex step6CommonScope14_valid b))) step6CommonPoint14 = true)
def step6CommonGroup14 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope14 step6CommonScope14_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint14
  (fun a => step6CommonGroup14_sources a 0) (fun b => step6CommonGroup14_neighbors b 0)

def step6CommonScope15 : Scope := ⟨0, 29, 29, 15⟩
theorem step6CommonScope15_valid : step6CommonScope15.Valid 59 59 := by decide +kernel

def step6CommonPoint15 : CommonPoint.Point := ⟨1715, 2868, 1000⟩
kernel_matrix step6CommonGroup15_sources : 29 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope15.sourceIndex step6CommonScope15_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope15.sourceIndex step6CommonScope15_valid a))) step6CommonPoint15 = true)
kernel_matrix step6CommonGroup15_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope15.neighborIndex step6CommonScope15_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope15.neighborIndex step6CommonScope15_valid b))) step6CommonPoint15 = true)
def step6CommonGroup15 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope15 step6CommonScope15_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint15
  (fun a => step6CommonGroup15_sources a 0) (fun b => step6CommonGroup15_neighbors b 0)

def step6CommonScope16 : Scope := ⟨0, 14, 44, 7⟩
theorem step6CommonScope16_valid : step6CommonScope16.Valid 59 59 := by decide +kernel

def step6CommonPoint16 : CommonPoint.Point := ⟨1794, 2937, 1000⟩
kernel_matrix step6CommonGroup16_sources : 14 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope16.sourceIndex step6CommonScope16_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope16.sourceIndex step6CommonScope16_valid a))) step6CommonPoint16 = true)
kernel_matrix step6CommonGroup16_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope16.neighborIndex step6CommonScope16_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope16.neighborIndex step6CommonScope16_valid b))) step6CommonPoint16 = true)
def step6CommonGroup16 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope16 step6CommonScope16_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint16
  (fun a => step6CommonGroup16_sources a 0) (fun b => step6CommonGroup16_neighbors b 0)

def step6CommonScope17 : Scope := ⟨0, 14, 51, 4⟩
theorem step6CommonScope17_valid : step6CommonScope17.Valid 59 59 := by decide +kernel

def step6CommonPoint17 : CommonPoint.Point := ⟨1808, 2965, 1000⟩
kernel_matrix step6CommonGroup17_sources : 14 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope17.sourceIndex step6CommonScope17_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope17.sourceIndex step6CommonScope17_valid a))) step6CommonPoint17 = true)
kernel_matrix step6CommonGroup17_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope17.neighborIndex step6CommonScope17_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope17.neighborIndex step6CommonScope17_valid b))) step6CommonPoint17 = true)
def step6CommonGroup17 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope17 step6CommonScope17_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint17
  (fun a => step6CommonGroup17_sources a 0) (fun b => step6CommonGroup17_neighbors b 0)

def step6CommonScope18 : Scope := ⟨0, 14, 55, 4⟩
theorem step6CommonScope18_valid : step6CommonScope18.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup18_checked : 14 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope18.sourceIndex step6CommonScope18_valid a))
    (step6CommonRawNeighbors (step6CommonScope18.neighborIndex step6CommonScope18_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope18.sourceIndex step6CommonScope18_valid a))
      (step6CommonNeighborAngles (step6CommonScope18.neighborIndex step6CommonScope18_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup18 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope18 step6CommonScope18_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup18_checked

def step6CommonScope19 : Scope := ⟨14, 7, 44, 7⟩
theorem step6CommonScope19_valid : step6CommonScope19.Valid 59 59 := by decide +kernel

def step6CommonPoint19 : CommonPoint.Point := ⟨1795, 2931, 1000⟩
kernel_matrix step6CommonGroup19_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope19.sourceIndex step6CommonScope19_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope19.sourceIndex step6CommonScope19_valid a))) step6CommonPoint19 = true)
kernel_matrix step6CommonGroup19_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope19.neighborIndex step6CommonScope19_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope19.neighborIndex step6CommonScope19_valid b))) step6CommonPoint19 = true)
def step6CommonGroup19 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope19 step6CommonScope19_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint19
  (fun a => step6CommonGroup19_sources a 0) (fun b => step6CommonGroup19_neighbors b 0)

def step6CommonScope20 : Scope := ⟨21, 4, 44, 7⟩
theorem step6CommonScope20_valid : step6CommonScope20.Valid 59 59 := by decide +kernel

def step6CommonPoint20 : CommonPoint.Point := ⟨1696, 2941, 1000⟩
kernel_matrix step6CommonGroup20_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope20.sourceIndex step6CommonScope20_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope20.sourceIndex step6CommonScope20_valid a))) step6CommonPoint20 = true)
kernel_matrix step6CommonGroup20_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope20.neighborIndex step6CommonScope20_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope20.neighborIndex step6CommonScope20_valid b))) step6CommonPoint20 = true)
def step6CommonGroup20 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope20 step6CommonScope20_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint20
  (fun a => step6CommonGroup20_sources a 0) (fun b => step6CommonGroup20_neighbors b 0)

def step6CommonScope21 : Scope := ⟨25, 4, 44, 7⟩
theorem step6CommonScope21_valid : step6CommonScope21.Valid 59 59 := by decide +kernel

def step6CommonPoint21 : CommonPoint.Point := ⟨1617, 2949, 1000⟩
kernel_matrix step6CommonGroup21_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope21.sourceIndex step6CommonScope21_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope21.sourceIndex step6CommonScope21_valid a))) step6CommonPoint21 = true)
kernel_matrix step6CommonGroup21_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope21.neighborIndex step6CommonScope21_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope21.neighborIndex step6CommonScope21_valid b))) step6CommonPoint21 = true)
def step6CommonGroup21 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope21 step6CommonScope21_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint21
  (fun a => step6CommonGroup21_sources a 0) (fun b => step6CommonGroup21_neighbors b 0)

def step6CommonScope22 : Scope := ⟨14, 15, 51, 8⟩
theorem step6CommonScope22_valid : step6CommonScope22.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup22_checked : 15 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope22.sourceIndex step6CommonScope22_valid a))
    (step6CommonRawNeighbors (step6CommonScope22.neighborIndex step6CommonScope22_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope22.sourceIndex step6CommonScope22_valid a))
      (step6CommonNeighborAngles (step6CommonScope22.neighborIndex step6CommonScope22_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup22 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope22 step6CommonScope22_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup22_checked

def step6CommonScope23 : Scope := ⟨29, 30, 29, 15⟩
theorem step6CommonScope23_valid : step6CommonScope23.Valid 59 59 := by decide +kernel

def step6CommonPoint23 : CommonPoint.Point := ⟨1526, 2913, 1000⟩
kernel_matrix step6CommonGroup23_sources : 30 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope23.sourceIndex step6CommonScope23_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope23.sourceIndex step6CommonScope23_valid a))) step6CommonPoint23 = true)
kernel_matrix step6CommonGroup23_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope23.neighborIndex step6CommonScope23_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope23.neighborIndex step6CommonScope23_valid b))) step6CommonPoint23 = true)
def step6CommonGroup23 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope23 step6CommonScope23_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint23
  (fun a => step6CommonGroup23_sources a 0) (fun b => step6CommonGroup23_neighbors b 0)

def step6CommonScope24 : Scope := ⟨29, 15, 44, 15⟩
theorem step6CommonScope24_valid : step6CommonScope24.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup24_checked : 15 × 15 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope24.sourceIndex step6CommonScope24_valid a))
    (step6CommonRawNeighbors (step6CommonScope24.neighborIndex step6CommonScope24_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope24.sourceIndex step6CommonScope24_valid a))
      (step6CommonNeighborAngles (step6CommonScope24.neighborIndex step6CommonScope24_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup24 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope24 step6CommonScope24_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup24_checked

def step6CommonScope25 : Scope := ⟨44, 7, 44, 7⟩
theorem step6CommonScope25_valid : step6CommonScope25.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup25_checked : 7 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope25.sourceIndex step6CommonScope25_valid a))
    (step6CommonRawNeighbors (step6CommonScope25.neighborIndex step6CommonScope25_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope25.sourceIndex step6CommonScope25_valid a))
      (step6CommonNeighborAngles (step6CommonScope25.neighborIndex step6CommonScope25_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup25 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope25 step6CommonScope25_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup25_checked

def step6CommonScope26 : Scope := ⟨51, 8, 44, 7⟩
theorem step6CommonScope26_valid : step6CommonScope26.Valid 59 59 := by decide +kernel

def step6CommonPoint26 : CommonPoint.Point := ⟨16744155, 29350403, 10000000⟩
kernel_matrix step6CommonGroup26_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step6CommonRawSources (step6CommonScope26.sourceIndex step6CommonScope26_valid a))
    (ownKeys (step6CommonSourceAngles (step6CommonScope26.sourceIndex step6CommonScope26_valid a))) step6CommonPoint26 = true)
kernel_matrix step6CommonGroup26_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step6CommonRawNeighbors (step6CommonScope26.neighborIndex step6CommonScope26_valid b))
    (ownKeys (step6CommonNeighborAngles (step6CommonScope26.neighborIndex step6CommonScope26_valid b))) step6CommonPoint26 = true)
def step6CommonGroup26 : CheckedGroup step6Sources step6Neighbors := pointGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope26 step6CommonScope26_valid
  (fun i => ownKeys (step6CommonSourceAngles i))
  (fun j => ownKeys (step6CommonNeighborAngles j)) step6CommonPoint26
  (fun a => step6CommonGroup26_sources a 0) (fun b => step6CommonGroup26_neighbors b 0)

def step6CommonScope27 : Scope := ⟨44, 15, 51, 8⟩
theorem step6CommonScope27_valid : step6CommonScope27.Valid 59 59 := by decide +kernel

kernel_matrix step6CommonGroup27_checked : 15 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step6CommonRawSources (step6CommonScope27.sourceIndex step6CommonScope27_valid a))
    (step6CommonRawNeighbors (step6CommonScope27.neighborIndex step6CommonScope27_valid b))
    (fanDirectionKey (step6CommonSourceAngles (step6CommonScope27.sourceIndex step6CommonScope27_valid a))
      (step6CommonNeighborAngles (step6CommonScope27.neighborIndex step6CommonScope27_valid b))) (fun key => (key + 128) % 256))
def step6CommonGroup27 : CheckedGroup step6Sources step6Neighbors := fallbackGroup
  step6Sources step6Neighbors
  step6CommonRawSources step6CommonRawNeighbors
  step6CommonRawSources_exact step6CommonRawNeighbors_exact
  step6CommonNeighborUnblocked step6CommonScope27 step6CommonScope27_valid
  step6CommonSourceAngles step6CommonNeighborAngles
  step6CommonSourceAngles_exact step6CommonNeighborAngles_exact
  step6CommonGroup27_checked

def step6CommonScopes : List Scope := [
  step6CommonScope0, step6CommonScope1, step6CommonScope2, step6CommonScope3, step6CommonScope4, step6CommonScope5, step6CommonScope6, step6CommonScope7, step6CommonScope8, step6CommonScope9, step6CommonScope10, step6CommonScope11, step6CommonScope12, step6CommonScope13, step6CommonScope14, step6CommonScope15, step6CommonScope16, step6CommonScope17, step6CommonScope18, step6CommonScope19, step6CommonScope20, step6CommonScope21, step6CommonScope22, step6CommonScope23, step6CommonScope24, step6CommonScope25, step6CommonScope26, step6CommonScope27]
def step6CommonGroups : List (CheckedGroup step6Sources step6Neighbors) := [
  step6CommonGroup0, step6CommonGroup1, step6CommonGroup2, step6CommonGroup3, step6CommonGroup4, step6CommonGroup5, step6CommonGroup6, step6CommonGroup7, step6CommonGroup8, step6CommonGroup9, step6CommonGroup10, step6CommonGroup11, step6CommonGroup12, step6CommonGroup13, step6CommonGroup14, step6CommonGroup15, step6CommonGroup16, step6CommonGroup17, step6CommonGroup18, step6CommonGroup19, step6CommonGroup20, step6CommonGroup21, step6CommonGroup22, step6CommonGroup23, step6CommonGroup24, step6CommonGroup25, step6CommonGroup26, step6CommonGroup27]
theorem step6CommonScopes_exact :
    step6CommonGroups.map CheckedGroup.scope = step6CommonScopes := rfl
kernel_matrix step6CommonCoverage : 59 × 59 => (fun i j =>
  ScopeCheck step6CommonScopes i.val j.val)
theorem step6_geometric_overlap (i : Fin 59) (j : Fin 59) :
    PairOverlaps (step6Sources i) (step6Neighbors j) :=
  groups_sound step6Sources step6Neighbors step6CommonGroups
    step6CommonScopes step6CommonScopes_exact step6CommonCoverage i j
#print axioms step6_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
