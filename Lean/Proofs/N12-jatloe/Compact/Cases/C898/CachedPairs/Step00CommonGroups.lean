import Compact.Cases.C898.CachedPairs.Step00CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step0CommonScope0 : Scope := ⟨0, 12, 0, 7⟩
theorem step0CommonScope0_valid : step0CommonScope0.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup0_checked : 12 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope0.sourceIndex step0CommonScope0_valid a))
    (step0CommonRawNeighbors (step0CommonScope0.neighborIndex step0CommonScope0_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope0.sourceIndex step0CommonScope0_valid a))
      (step0CommonNeighborAngles (step0CommonScope0.neighborIndex step0CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup0 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope0 step0CommonScope0_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup0_checked

def step0CommonScope1 : Scope := ⟨0, 12, 7, 3⟩
theorem step0CommonScope1_valid : step0CommonScope1.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup1_checked : 12 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope1.sourceIndex step0CommonScope1_valid a))
    (step0CommonRawNeighbors (step0CommonScope1.neighborIndex step0CommonScope1_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope1.sourceIndex step0CommonScope1_valid a))
      (step0CommonNeighborAngles (step0CommonScope1.neighborIndex step0CommonScope1_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup1 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope1 step0CommonScope1_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup1_checked

def step0CommonScope2 : Scope := ⟨0, 12, 10, 4⟩
theorem step0CommonScope2_valid : step0CommonScope2.Valid 50 59 := by decide +kernel

def step0CommonPoint2 : CommonPoint.Point := ⟨409, 968, 500⟩
kernel_matrix step0CommonGroup2_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope2.sourceIndex step0CommonScope2_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope2.sourceIndex step0CommonScope2_valid a))) step0CommonPoint2 = true)
kernel_matrix step0CommonGroup2_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope2.neighborIndex step0CommonScope2_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope2.neighborIndex step0CommonScope2_valid b))) step0CommonPoint2 = true)
def step0CommonGroup2 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope2 step0CommonScope2_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint2
  (fun a => step0CommonGroup2_sources a 0) (fun b => step0CommonGroup2_neighbors b 0)

def step0CommonScope3 : Scope := ⟨12, 13, 0, 7⟩
theorem step0CommonScope3_valid : step0CommonScope3.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup3_checked : 13 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope3.sourceIndex step0CommonScope3_valid a))
    (step0CommonRawNeighbors (step0CommonScope3.neighborIndex step0CommonScope3_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope3.sourceIndex step0CommonScope3_valid a))
      (step0CommonNeighborAngles (step0CommonScope3.neighborIndex step0CommonScope3_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup3 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope3 step0CommonScope3_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup3_checked

def step0CommonScope4 : Scope := ⟨12, 13, 7, 3⟩
theorem step0CommonScope4_valid : step0CommonScope4.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup4_checked : 13 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope4.sourceIndex step0CommonScope4_valid a))
    (step0CommonRawNeighbors (step0CommonScope4.neighborIndex step0CommonScope4_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope4.sourceIndex step0CommonScope4_valid a))
      (step0CommonNeighborAngles (step0CommonScope4.neighborIndex step0CommonScope4_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup4 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope4 step0CommonScope4_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup4_checked

def step0CommonScope5 : Scope := ⟨12, 13, 10, 4⟩
theorem step0CommonScope5_valid : step0CommonScope5.Valid 50 59 := by decide +kernel

def step0CommonPoint5 : CommonPoint.Point := ⟨773, 1923, 1000⟩
kernel_matrix step0CommonGroup5_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope5.sourceIndex step0CommonScope5_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope5.sourceIndex step0CommonScope5_valid a))) step0CommonPoint5 = true)
kernel_matrix step0CommonGroup5_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope5.neighborIndex step0CommonScope5_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope5.neighborIndex step0CommonScope5_valid b))) step0CommonPoint5 = true)
def step0CommonGroup5 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope5 step0CommonScope5_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint5
  (fun a => step0CommonGroup5_sources a 0) (fun b => step0CommonGroup5_neighbors b 0)

def step0CommonScope6 : Scope := ⟨25, 12, 0, 7⟩
theorem step0CommonScope6_valid : step0CommonScope6.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup6_checked : 12 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope6.sourceIndex step0CommonScope6_valid a))
    (step0CommonRawNeighbors (step0CommonScope6.neighborIndex step0CommonScope6_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope6.sourceIndex step0CommonScope6_valid a))
      (step0CommonNeighborAngles (step0CommonScope6.neighborIndex step0CommonScope6_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup6 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope6 step0CommonScope6_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup6_checked

def step0CommonScope7 : Scope := ⟨25, 12, 7, 3⟩
theorem step0CommonScope7_valid : step0CommonScope7.Valid 50 59 := by decide +kernel

def step0CommonPoint7 : CommonPoint.Point := ⟨372, 975, 500⟩
kernel_matrix step0CommonGroup7_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope7.sourceIndex step0CommonScope7_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope7.sourceIndex step0CommonScope7_valid a))) step0CommonPoint7 = true)
kernel_matrix step0CommonGroup7_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope7.neighborIndex step0CommonScope7_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope7.neighborIndex step0CommonScope7_valid b))) step0CommonPoint7 = true)
def step0CommonGroup7 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope7 step0CommonScope7_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint7
  (fun a => step0CommonGroup7_sources a 0) (fun b => step0CommonGroup7_neighbors b 0)

def step0CommonScope8 : Scope := ⟨25, 12, 10, 4⟩
theorem step0CommonScope8_valid : step0CommonScope8.Valid 50 59 := by decide +kernel

def step0CommonPoint8 : CommonPoint.Point := ⟨769, 1928, 1000⟩
kernel_matrix step0CommonGroup8_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope8.sourceIndex step0CommonScope8_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope8.sourceIndex step0CommonScope8_valid a))) step0CommonPoint8 = true)
kernel_matrix step0CommonGroup8_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope8.neighborIndex step0CommonScope8_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope8.neighborIndex step0CommonScope8_valid b))) step0CommonPoint8 = true)
def step0CommonGroup8 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope8 step0CommonScope8_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint8
  (fun a => step0CommonGroup8_sources a 0) (fun b => step0CommonGroup8_neighbors b 0)

def step0CommonScope9 : Scope := ⟨37, 13, 0, 7⟩
theorem step0CommonScope9_valid : step0CommonScope9.Valid 50 59 := by decide +kernel

def step0CommonPoint9 : CommonPoint.Point := ⟨716, 2013, 1000⟩
kernel_matrix step0CommonGroup9_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope9.sourceIndex step0CommonScope9_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope9.sourceIndex step0CommonScope9_valid a))) step0CommonPoint9 = true)
kernel_matrix step0CommonGroup9_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope9.neighborIndex step0CommonScope9_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope9.neighborIndex step0CommonScope9_valid b))) step0CommonPoint9 = true)
def step0CommonGroup9 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope9 step0CommonScope9_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint9
  (fun a => step0CommonGroup9_sources a 0) (fun b => step0CommonGroup9_neighbors b 0)

def step0CommonScope10 : Scope := ⟨37, 13, 7, 7⟩
theorem step0CommonScope10_valid : step0CommonScope10.Valid 50 59 := by decide +kernel

def step0CommonPoint10 : CommonPoint.Point := ⟨757, 1976, 1000⟩
kernel_matrix step0CommonGroup10_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope10.sourceIndex step0CommonScope10_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope10.sourceIndex step0CommonScope10_valid a))) step0CommonPoint10 = true)
kernel_matrix step0CommonGroup10_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope10.neighborIndex step0CommonScope10_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope10.neighborIndex step0CommonScope10_valid b))) step0CommonPoint10 = true)
def step0CommonGroup10 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope10 step0CommonScope10_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint10
  (fun a => step0CommonGroup10_sources a 0) (fun b => step0CommonGroup10_neighbors b 0)

def step0CommonScope11 : Scope := ⟨0, 50, 14, 15⟩
theorem step0CommonScope11_valid : step0CommonScope11.Valid 50 59 := by decide +kernel

def step0CommonPoint11 : CommonPoint.Point := ⟨387, 958, 500⟩
kernel_matrix step0CommonGroup11_sources : 50 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope11.sourceIndex step0CommonScope11_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope11.sourceIndex step0CommonScope11_valid a))) step0CommonPoint11 = true)
kernel_matrix step0CommonGroup11_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope11.neighborIndex step0CommonScope11_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope11.neighborIndex step0CommonScope11_valid b))) step0CommonPoint11 = true)
def step0CommonGroup11 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope11 step0CommonScope11_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint11
  (fun a => step0CommonGroup11_sources a 0) (fun b => step0CommonGroup11_neighbors b 0)

def step0CommonScope12 : Scope := ⟨0, 6, 29, 15⟩
theorem step0CommonScope12_valid : step0CommonScope12.Valid 50 59 := by decide +kernel

def step0CommonPoint12 : CommonPoint.Point := ⟨899, 1978, 1000⟩
kernel_matrix step0CommonGroup12_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope12.sourceIndex step0CommonScope12_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope12.sourceIndex step0CommonScope12_valid a))) step0CommonPoint12 = true)
kernel_matrix step0CommonGroup12_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope12.neighborIndex step0CommonScope12_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope12.neighborIndex step0CommonScope12_valid b))) step0CommonPoint12 = true)
def step0CommonGroup12 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope12 step0CommonScope12_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint12
  (fun a => step0CommonGroup12_sources a 0) (fun b => step0CommonGroup12_neighbors b 0)

def step0CommonScope13 : Scope := ⟨6, 3, 29, 15⟩
theorem step0CommonScope13_valid : step0CommonScope13.Valid 50 59 := by decide +kernel

def step0CommonPoint13 : CommonPoint.Point := ⟨9003, 19757, 10000⟩
kernel_matrix step0CommonGroup13_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope13.sourceIndex step0CommonScope13_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope13.sourceIndex step0CommonScope13_valid a))) step0CommonPoint13 = true)
kernel_matrix step0CommonGroup13_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope13.neighborIndex step0CommonScope13_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope13.neighborIndex step0CommonScope13_valid b))) step0CommonPoint13 = true)
def step0CommonGroup13 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope13 step0CommonScope13_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint13
  (fun a => step0CommonGroup13_sources a 0) (fun b => step0CommonGroup13_neighbors b 0)

def step0CommonScope14 : Scope := ⟨9, 3, 29, 15⟩
theorem step0CommonScope14_valid : step0CommonScope14.Valid 50 59 := by decide +kernel

def step0CommonPoint14 : CommonPoint.Point := ⟨433, 994, 500⟩
kernel_matrix step0CommonGroup14_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope14.sourceIndex step0CommonScope14_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope14.sourceIndex step0CommonScope14_valid a))) step0CommonPoint14 = true)
kernel_matrix step0CommonGroup14_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope14.neighborIndex step0CommonScope14_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope14.neighborIndex step0CommonScope14_valid b))) step0CommonPoint14 = true)
def step0CommonGroup14 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope14 step0CommonScope14_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint14
  (fun a => step0CommonGroup14_sources a 0) (fun b => step0CommonGroup14_neighbors b 0)

def step0CommonScope15 : Scope := ⟨12, 6, 29, 7⟩
theorem step0CommonScope15_valid : step0CommonScope15.Valid 50 59 := by decide +kernel

def step0CommonPoint15 : CommonPoint.Point := ⟨813, 1956, 1000⟩
kernel_matrix step0CommonGroup15_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope15.sourceIndex step0CommonScope15_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope15.sourceIndex step0CommonScope15_valid a))) step0CommonPoint15 = true)
kernel_matrix step0CommonGroup15_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope15.neighborIndex step0CommonScope15_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope15.neighborIndex step0CommonScope15_valid b))) step0CommonPoint15 = true)
def step0CommonGroup15 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope15 step0CommonScope15_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint15
  (fun a => step0CommonGroup15_sources a 0) (fun b => step0CommonGroup15_neighbors b 0)

def step0CommonScope16 : Scope := ⟨18, 7, 29, 3⟩
theorem step0CommonScope16_valid : step0CommonScope16.Valid 50 59 := by decide +kernel

def step0CommonPoint16 : CommonPoint.Point := ⟨183, 491, 250⟩
kernel_matrix step0CommonGroup16_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope16.sourceIndex step0CommonScope16_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope16.sourceIndex step0CommonScope16_valid a))) step0CommonPoint16 = true)
kernel_matrix step0CommonGroup16_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope16.neighborIndex step0CommonScope16_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope16.neighborIndex step0CommonScope16_valid b))) step0CommonPoint16 = true)
def step0CommonGroup16 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope16 step0CommonScope16_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint16
  (fun a => step0CommonGroup16_sources a 0) (fun b => step0CommonGroup16_neighbors b 0)

def step0CommonScope17 : Scope := ⟨18, 7, 32, 4⟩
theorem step0CommonScope17_valid : step0CommonScope17.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup17_checked : 7 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope17.sourceIndex step0CommonScope17_valid a))
    (step0CommonRawNeighbors (step0CommonScope17.neighborIndex step0CommonScope17_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope17.sourceIndex step0CommonScope17_valid a))
      (step0CommonNeighborAngles (step0CommonScope17.neighborIndex step0CommonScope17_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup17 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope17 step0CommonScope17_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup17_checked

def step0CommonScope18 : Scope := ⟨12, 13, 36, 8⟩
theorem step0CommonScope18_valid : step0CommonScope18.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup18_checked : 13 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope18.sourceIndex step0CommonScope18_valid a))
    (step0CommonRawNeighbors (step0CommonScope18.neighborIndex step0CommonScope18_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope18.sourceIndex step0CommonScope18_valid a))
      (step0CommonNeighborAngles (step0CommonScope18.neighborIndex step0CommonScope18_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup18 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope18 step0CommonScope18_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup18_checked

def step0CommonScope19 : Scope := ⟨0, 6, 44, 7⟩
theorem step0CommonScope19_valid : step0CommonScope19.Valid 50 59 := by decide +kernel

def step0CommonPoint19 : CommonPoint.Point := ⟨957, 1996, 1000⟩
kernel_matrix step0CommonGroup19_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope19.sourceIndex step0CommonScope19_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope19.sourceIndex step0CommonScope19_valid a))) step0CommonPoint19 = true)
kernel_matrix step0CommonGroup19_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope19.neighborIndex step0CommonScope19_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope19.neighborIndex step0CommonScope19_valid b))) step0CommonPoint19 = true)
def step0CommonGroup19 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope19 step0CommonScope19_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint19
  (fun a => step0CommonGroup19_sources a 0) (fun b => step0CommonGroup19_neighbors b 0)

def step0CommonScope20 : Scope := ⟨6, 6, 44, 7⟩
theorem step0CommonScope20_valid : step0CommonScope20.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup20_checked : 6 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope20.sourceIndex step0CommonScope20_valid a))
    (step0CommonRawNeighbors (step0CommonScope20.neighborIndex step0CommonScope20_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope20.sourceIndex step0CommonScope20_valid a))
      (step0CommonNeighborAngles (step0CommonScope20.neighborIndex step0CommonScope20_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup20 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope20 step0CommonScope20_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup20_checked

def step0CommonScope21 : Scope := ⟨0, 12, 51, 8⟩
theorem step0CommonScope21_valid : step0CommonScope21.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup21_checked : 12 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope21.sourceIndex step0CommonScope21_valid a))
    (step0CommonRawNeighbors (step0CommonScope21.neighborIndex step0CommonScope21_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope21.sourceIndex step0CommonScope21_valid a))
      (step0CommonNeighborAngles (step0CommonScope21.neighborIndex step0CommonScope21_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup21 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope21 step0CommonScope21_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup21_checked

def step0CommonScope22 : Scope := ⟨12, 13, 44, 15⟩
theorem step0CommonScope22_valid : step0CommonScope22.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup22_checked : 13 × 15 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope22.sourceIndex step0CommonScope22_valid a))
    (step0CommonRawNeighbors (step0CommonScope22.neighborIndex step0CommonScope22_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope22.sourceIndex step0CommonScope22_valid a))
      (step0CommonNeighborAngles (step0CommonScope22.neighborIndex step0CommonScope22_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup22 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope22 step0CommonScope22_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup22_checked

def step0CommonScope23 : Scope := ⟨25, 12, 29, 3⟩
theorem step0CommonScope23_valid : step0CommonScope23.Valid 50 59 := by decide +kernel

def step0CommonPoint23 : CommonPoint.Point := ⟨661, 2005, 1000⟩
kernel_matrix step0CommonGroup23_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope23.sourceIndex step0CommonScope23_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope23.sourceIndex step0CommonScope23_valid a))) step0CommonPoint23 = true)
kernel_matrix step0CommonGroup23_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope23.neighborIndex step0CommonScope23_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope23.neighborIndex step0CommonScope23_valid b))) step0CommonPoint23 = true)
def step0CommonGroup23 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope23 step0CommonScope23_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint23
  (fun a => step0CommonGroup23_sources a 0) (fun b => step0CommonGroup23_neighbors b 0)

def step0CommonScope24 : Scope := ⟨25, 12, 32, 4⟩
theorem step0CommonScope24_valid : step0CommonScope24.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup24_checked : 12 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope24.sourceIndex step0CommonScope24_valid a))
    (step0CommonRawNeighbors (step0CommonScope24.neighborIndex step0CommonScope24_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope24.sourceIndex step0CommonScope24_valid a))
      (step0CommonNeighborAngles (step0CommonScope24.neighborIndex step0CommonScope24_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup24 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope24 step0CommonScope24_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup24_checked

def step0CommonScope25 : Scope := ⟨25, 12, 36, 8⟩
theorem step0CommonScope25_valid : step0CommonScope25.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup25_checked : 12 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope25.sourceIndex step0CommonScope25_valid a))
    (step0CommonRawNeighbors (step0CommonScope25.neighborIndex step0CommonScope25_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope25.sourceIndex step0CommonScope25_valid a))
      (step0CommonNeighborAngles (step0CommonScope25.neighborIndex step0CommonScope25_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup25 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope25 step0CommonScope25_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup25_checked

def step0CommonScope26 : Scope := ⟨37, 6, 29, 7⟩
theorem step0CommonScope26_valid : step0CommonScope26.Valid 50 59 := by decide +kernel

def step0CommonPoint26 : CommonPoint.Point := ⟨183, 500, 250⟩
kernel_matrix step0CommonGroup26_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope26.sourceIndex step0CommonScope26_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope26.sourceIndex step0CommonScope26_valid a))) step0CommonPoint26 = true)
kernel_matrix step0CommonGroup26_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope26.neighborIndex step0CommonScope26_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope26.neighborIndex step0CommonScope26_valid b))) step0CommonPoint26 = true)
def step0CommonGroup26 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope26 step0CommonScope26_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint26
  (fun a => step0CommonGroup26_sources a 0) (fun b => step0CommonGroup26_neighbors b 0)

def step0CommonScope27 : Scope := ⟨37, 6, 36, 8⟩
theorem step0CommonScope27_valid : step0CommonScope27.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup27_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope27.sourceIndex step0CommonScope27_valid a))
    (step0CommonRawNeighbors (step0CommonScope27.neighborIndex step0CommonScope27_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope27.sourceIndex step0CommonScope27_valid a))
      (step0CommonNeighborAngles (step0CommonScope27.neighborIndex step0CommonScope27_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup27 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope27 step0CommonScope27_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup27_checked

def step0CommonScope28 : Scope := ⟨43, 7, 29, 15⟩
theorem step0CommonScope28_valid : step0CommonScope28.Valid 50 59 := by decide +kernel

def step0CommonPoint28 : CommonPoint.Point := ⟨811, 2002, 1000⟩
kernel_matrix step0CommonGroup28_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope28.sourceIndex step0CommonScope28_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope28.sourceIndex step0CommonScope28_valid a))) step0CommonPoint28 = true)
kernel_matrix step0CommonGroup28_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope28.neighborIndex step0CommonScope28_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope28.neighborIndex step0CommonScope28_valid b))) step0CommonPoint28 = true)
def step0CommonGroup28 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope28 step0CommonScope28_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint28
  (fun a => step0CommonGroup28_sources a 0) (fun b => step0CommonGroup28_neighbors b 0)

def step0CommonScope29 : Scope := ⟨25, 12, 44, 15⟩
theorem step0CommonScope29_valid : step0CommonScope29.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup29_checked : 12 × 15 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope29.sourceIndex step0CommonScope29_valid a))
    (step0CommonRawNeighbors (step0CommonScope29.neighborIndex step0CommonScope29_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope29.sourceIndex step0CommonScope29_valid a))
      (step0CommonNeighborAngles (step0CommonScope29.neighborIndex step0CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup29 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope29 step0CommonScope29_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup29_checked

def step0CommonScope30 : Scope := ⟨37, 6, 44, 7⟩
theorem step0CommonScope30_valid : step0CommonScope30.Valid 50 59 := by decide +kernel

def step0CommonPoint30 : CommonPoint.Point := ⟨6090, 20563, 10000⟩
kernel_matrix step0CommonGroup30_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope30.sourceIndex step0CommonScope30_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope30.sourceIndex step0CommonScope30_valid a))) step0CommonPoint30 = true)
kernel_matrix step0CommonGroup30_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope30.neighborIndex step0CommonScope30_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope30.neighborIndex step0CommonScope30_valid b))) step0CommonPoint30 = true)
def step0CommonGroup30 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope30 step0CommonScope30_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint30
  (fun a => step0CommonGroup30_sources a 0) (fun b => step0CommonGroup30_neighbors b 0)

def step0CommonScope31 : Scope := ⟨43, 7, 44, 7⟩
theorem step0CommonScope31_valid : step0CommonScope31.Valid 50 59 := by decide +kernel

kernel_matrix step0CommonGroup31_checked : 7 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step0CommonRawSources (step0CommonScope31.sourceIndex step0CommonScope31_valid a))
    (step0CommonRawNeighbors (step0CommonScope31.neighborIndex step0CommonScope31_valid b))
    (fanDirectionKey (step0CommonSourceAngles (step0CommonScope31.sourceIndex step0CommonScope31_valid a))
      (step0CommonNeighborAngles (step0CommonScope31.neighborIndex step0CommonScope31_valid b))) (fun key => (key + 128) % 256))
def step0CommonGroup31 : CheckedGroup step0Sources step0Neighbors := fallbackGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope31 step0CommonScope31_valid
  step0CommonSourceAngles step0CommonNeighborAngles
  step0CommonSourceAngles_exact step0CommonNeighborAngles_exact
  step0CommonGroup31_checked

def step0CommonScope32 : Scope := ⟨37, 13, 51, 8⟩
theorem step0CommonScope32_valid : step0CommonScope32.Valid 50 59 := by decide +kernel

def step0CommonPoint32 : CommonPoint.Point := ⟨331, 1017, 500⟩
kernel_matrix step0CommonGroup32_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step0CommonRawSources (step0CommonScope32.sourceIndex step0CommonScope32_valid a))
    (ownKeys (step0CommonSourceAngles (step0CommonScope32.sourceIndex step0CommonScope32_valid a))) step0CommonPoint32 = true)
kernel_matrix step0CommonGroup32_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step0CommonRawNeighbors (step0CommonScope32.neighborIndex step0CommonScope32_valid b))
    (ownKeys (step0CommonNeighborAngles (step0CommonScope32.neighborIndex step0CommonScope32_valid b))) step0CommonPoint32 = true)
def step0CommonGroup32 : CheckedGroup step0Sources step0Neighbors := pointGroup
  step0Sources step0Neighbors
  step0CommonRawSources step0CommonRawNeighbors
  step0CommonRawSources_exact step0CommonRawNeighbors_exact
  step0CommonNeighborUnblocked step0CommonScope32 step0CommonScope32_valid
  (fun i => ownKeys (step0CommonSourceAngles i))
  (fun j => ownKeys (step0CommonNeighborAngles j)) step0CommonPoint32
  (fun a => step0CommonGroup32_sources a 0) (fun b => step0CommonGroup32_neighbors b 0)

def step0CommonScopes : List Scope := [
  step0CommonScope0, step0CommonScope1, step0CommonScope2, step0CommonScope3, step0CommonScope4, step0CommonScope5, step0CommonScope6, step0CommonScope7, step0CommonScope8, step0CommonScope9, step0CommonScope10, step0CommonScope11, step0CommonScope12, step0CommonScope13, step0CommonScope14, step0CommonScope15, step0CommonScope16, step0CommonScope17, step0CommonScope18, step0CommonScope19, step0CommonScope20, step0CommonScope21, step0CommonScope22, step0CommonScope23, step0CommonScope24, step0CommonScope25, step0CommonScope26, step0CommonScope27, step0CommonScope28, step0CommonScope29, step0CommonScope30, step0CommonScope31, step0CommonScope32]
def step0CommonGroups : List (CheckedGroup step0Sources step0Neighbors) := [
  step0CommonGroup0, step0CommonGroup1, step0CommonGroup2, step0CommonGroup3, step0CommonGroup4, step0CommonGroup5, step0CommonGroup6, step0CommonGroup7, step0CommonGroup8, step0CommonGroup9, step0CommonGroup10, step0CommonGroup11, step0CommonGroup12, step0CommonGroup13, step0CommonGroup14, step0CommonGroup15, step0CommonGroup16, step0CommonGroup17, step0CommonGroup18, step0CommonGroup19, step0CommonGroup20, step0CommonGroup21, step0CommonGroup22, step0CommonGroup23, step0CommonGroup24, step0CommonGroup25, step0CommonGroup26, step0CommonGroup27, step0CommonGroup28, step0CommonGroup29, step0CommonGroup30, step0CommonGroup31, step0CommonGroup32]
theorem step0CommonScopes_exact :
    step0CommonGroups.map CheckedGroup.scope = step0CommonScopes := rfl
kernel_matrix step0CommonCoverage : 50 × 59 => (fun i j =>
  ScopeCheck step0CommonScopes i.val j.val)
theorem step0_geometric_overlap (i : Fin 50) (j : Fin 59) :
    PairOverlaps (step0Sources i) (step0Neighbors j) :=
  groups_sound step0Sources step0Neighbors step0CommonGroups
    step0CommonScopes step0CommonScopes_exact step0CommonCoverage i j
#print axioms step0_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
