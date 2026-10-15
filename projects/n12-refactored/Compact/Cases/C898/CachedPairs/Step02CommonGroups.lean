import Compact.Cases.C898.CachedPairs.Step02CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step2CommonScope0 : Scope := ⟨0, 23, 0, 14⟩
theorem step2CommonScope0_valid : step2CommonScope0.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup0_checked : 23 × 14 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope0.sourceIndex step2CommonScope0_valid a))
    (step2CommonRawNeighbors (step2CommonScope0.neighborIndex step2CommonScope0_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope0.sourceIndex step2CommonScope0_valid a))
      (step2CommonNeighborAngles (step2CommonScope0.neighborIndex step2CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup0 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope0 step2CommonScope0_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup0_checked

def step2CommonScope1 : Scope := ⟨0, 23, 14, 3⟩
theorem step2CommonScope1_valid : step2CommonScope1.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup1_checked : 23 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope1.sourceIndex step2CommonScope1_valid a))
    (step2CommonRawNeighbors (step2CommonScope1.neighborIndex step2CommonScope1_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope1.sourceIndex step2CommonScope1_valid a))
      (step2CommonNeighborAngles (step2CommonScope1.neighborIndex step2CommonScope1_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup1 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope1 step2CommonScope1_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup1_checked

def step2CommonScope2 : Scope := ⟨0, 23, 17, 4⟩
theorem step2CommonScope2_valid : step2CommonScope2.Valid 47 59 := by decide +kernel

def step2CommonPoint2 : CommonPoint.Point := ⟨1018, 1633, 500⟩
kernel_matrix step2CommonGroup2_sources : 23 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope2.sourceIndex step2CommonScope2_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope2.sourceIndex step2CommonScope2_valid a))) step2CommonPoint2 = true)
kernel_matrix step2CommonGroup2_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope2.neighborIndex step2CommonScope2_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope2.neighborIndex step2CommonScope2_valid b))) step2CommonPoint2 = true)
def step2CommonGroup2 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope2 step2CommonScope2_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint2
  (fun a => step2CommonGroup2_sources a 0) (fun b => step2CommonGroup2_neighbors b 0)

def step2CommonScope3 : Scope := ⟨0, 23, 21, 8⟩
theorem step2CommonScope3_valid : step2CommonScope3.Valid 47 59 := by decide +kernel

def step2CommonPoint3 : CommonPoint.Point := ⟨2061, 3247, 1000⟩
kernel_matrix step2CommonGroup3_sources : 23 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope3.sourceIndex step2CommonScope3_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope3.sourceIndex step2CommonScope3_valid a))) step2CommonPoint3 = true)
kernel_matrix step2CommonGroup3_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope3.neighborIndex step2CommonScope3_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope3.neighborIndex step2CommonScope3_valid b))) step2CommonPoint3 = true)
def step2CommonGroup3 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope3 step2CommonScope3_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint3
  (fun a => step2CommonGroup3_sources a 0) (fun b => step2CommonGroup3_neighbors b 0)

def step2CommonScope4 : Scope := ⟨23, 12, 0, 14⟩
theorem step2CommonScope4_valid : step2CommonScope4.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup4_checked : 12 × 14 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope4.sourceIndex step2CommonScope4_valid a))
    (step2CommonRawNeighbors (step2CommonScope4.neighborIndex step2CommonScope4_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope4.sourceIndex step2CommonScope4_valid a))
      (step2CommonNeighborAngles (step2CommonScope4.neighborIndex step2CommonScope4_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup4 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope4 step2CommonScope4_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup4_checked

def step2CommonScope5 : Scope := ⟨35, 6, 0, 7⟩
theorem step2CommonScope5_valid : step2CommonScope5.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup5_checked : 6 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope5.sourceIndex step2CommonScope5_valid a))
    (step2CommonRawNeighbors (step2CommonScope5.neighborIndex step2CommonScope5_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope5.sourceIndex step2CommonScope5_valid a))
      (step2CommonNeighborAngles (step2CommonScope5.neighborIndex step2CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup5 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope5 step2CommonScope5_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup5_checked

def step2CommonScope6 : Scope := ⟨41, 6, 0, 3⟩
theorem step2CommonScope6_valid : step2CommonScope6.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup6_checked : 6 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope6.sourceIndex step2CommonScope6_valid a))
    (step2CommonRawNeighbors (step2CommonScope6.neighborIndex step2CommonScope6_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope6.sourceIndex step2CommonScope6_valid a))
      (step2CommonNeighborAngles (step2CommonScope6.neighborIndex step2CommonScope6_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup6 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope6 step2CommonScope6_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup6_checked

def step2CommonScope7 : Scope := ⟨41, 6, 3, 4⟩
theorem step2CommonScope7_valid : step2CommonScope7.Valid 47 59 := by decide +kernel

def step2CommonPoint7 : CommonPoint.Point := ⟨1995, 3039, 1000⟩
kernel_matrix step2CommonGroup7_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope7.sourceIndex step2CommonScope7_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope7.sourceIndex step2CommonScope7_valid a))) step2CommonPoint7 = true)
kernel_matrix step2CommonGroup7_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope7.neighborIndex step2CommonScope7_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope7.neighborIndex step2CommonScope7_valid b))) step2CommonPoint7 = true)
def step2CommonGroup7 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope7 step2CommonScope7_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint7
  (fun a => step2CommonGroup7_sources a 0) (fun b => step2CommonGroup7_neighbors b 0)

def step2CommonScope8 : Scope := ⟨35, 12, 7, 7⟩
theorem step2CommonScope8_valid : step2CommonScope8.Valid 47 59 := by decide +kernel

def step2CommonPoint8 : CommonPoint.Point := ⟨20141, 30782, 10000⟩
kernel_matrix step2CommonGroup8_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope8.sourceIndex step2CommonScope8_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope8.sourceIndex step2CommonScope8_valid a))) step2CommonPoint8 = true)
kernel_matrix step2CommonGroup8_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope8.neighborIndex step2CommonScope8_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope8.neighborIndex step2CommonScope8_valid b))) step2CommonPoint8 = true)
def step2CommonGroup8 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope8 step2CommonScope8_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint8
  (fun a => step2CommonGroup8_sources a 0) (fun b => step2CommonGroup8_neighbors b 0)

def step2CommonScope9 : Scope := ⟨23, 24, 14, 1⟩
theorem step2CommonScope9_valid : step2CommonScope9.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup9_checked : 24 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope9.sourceIndex step2CommonScope9_valid a))
    (step2CommonRawNeighbors (step2CommonScope9.neighborIndex step2CommonScope9_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope9.sourceIndex step2CommonScope9_valid a))
      (step2CommonNeighborAngles (step2CommonScope9.neighborIndex step2CommonScope9_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup9 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope9 step2CommonScope9_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup9_checked

def step2CommonScope10 : Scope := ⟨23, 24, 15, 2⟩
theorem step2CommonScope10_valid : step2CommonScope10.Valid 47 59 := by decide +kernel

def step2CommonPoint10 : CommonPoint.Point := ⟨1033, 1582, 500⟩
kernel_matrix step2CommonGroup10_sources : 24 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope10.sourceIndex step2CommonScope10_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope10.sourceIndex step2CommonScope10_valid a))) step2CommonPoint10 = true)
kernel_matrix step2CommonGroup10_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope10.neighborIndex step2CommonScope10_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope10.neighborIndex step2CommonScope10_valid b))) step2CommonPoint10 = true)
def step2CommonGroup10 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope10 step2CommonScope10_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint10
  (fun a => step2CommonGroup10_sources a 0) (fun b => step2CommonGroup10_neighbors b 0)

def step2CommonScope11 : Scope := ⟨23, 24, 17, 4⟩
theorem step2CommonScope11_valid : step2CommonScope11.Valid 47 59 := by decide +kernel

def step2CommonPoint11 : CommonPoint.Point := ⟨2080, 3169, 1000⟩
kernel_matrix step2CommonGroup11_sources : 24 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope11.sourceIndex step2CommonScope11_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope11.sourceIndex step2CommonScope11_valid a))) step2CommonPoint11 = true)
kernel_matrix step2CommonGroup11_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope11.neighborIndex step2CommonScope11_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope11.neighborIndex step2CommonScope11_valid b))) step2CommonPoint11 = true)
def step2CommonGroup11 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope11 step2CommonScope11_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint11
  (fun a => step2CommonGroup11_sources a 0) (fun b => step2CommonGroup11_neighbors b 0)

def step2CommonScope12 : Scope := ⟨23, 24, 21, 8⟩
theorem step2CommonScope12_valid : step2CommonScope12.Valid 47 59 := by decide +kernel

def step2CommonPoint12 : CommonPoint.Point := ⟨523, 806, 250⟩
kernel_matrix step2CommonGroup12_sources : 24 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope12.sourceIndex step2CommonScope12_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope12.sourceIndex step2CommonScope12_valid a))) step2CommonPoint12 = true)
kernel_matrix step2CommonGroup12_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope12.neighborIndex step2CommonScope12_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope12.neighborIndex step2CommonScope12_valid b))) step2CommonPoint12 = true)
def step2CommonGroup12 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope12 step2CommonScope12_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint12
  (fun a => step2CommonGroup12_sources a 0) (fun b => step2CommonGroup12_neighbors b 0)

def step2CommonScope13 : Scope := ⟨0, 23, 29, 15⟩
theorem step2CommonScope13_valid : step2CommonScope13.Valid 47 59 := by decide +kernel

def step2CommonPoint13 : CommonPoint.Point := ⟨2059, 3244, 1000⟩
kernel_matrix step2CommonGroup13_sources : 23 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope13.sourceIndex step2CommonScope13_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope13.sourceIndex step2CommonScope13_valid a))) step2CommonPoint13 = true)
kernel_matrix step2CommonGroup13_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope13.neighborIndex step2CommonScope13_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope13.neighborIndex step2CommonScope13_valid b))) step2CommonPoint13 = true)
def step2CommonGroup13 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope13 step2CommonScope13_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint13
  (fun a => step2CommonGroup13_sources a 0) (fun b => step2CommonGroup13_neighbors b 0)

def step2CommonScope14 : Scope := ⟨0, 23, 44, 7⟩
theorem step2CommonScope14_valid : step2CommonScope14.Valid 47 59 := by decide +kernel

def step2CommonPoint14 : CommonPoint.Point := ⟨2028, 3275, 1000⟩
kernel_matrix step2CommonGroup14_sources : 23 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope14.sourceIndex step2CommonScope14_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope14.sourceIndex step2CommonScope14_valid a))) step2CommonPoint14 = true)
kernel_matrix step2CommonGroup14_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope14.neighborIndex step2CommonScope14_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope14.neighborIndex step2CommonScope14_valid b))) step2CommonPoint14 = true)
def step2CommonGroup14 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope14 step2CommonScope14_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint14
  (fun a => step2CommonGroup14_sources a 0) (fun b => step2CommonGroup14_neighbors b 0)

def step2CommonScope15 : Scope := ⟨0, 5, 51, 8⟩
theorem step2CommonScope15_valid : step2CommonScope15.Valid 47 59 := by decide +kernel

def step2CommonPoint15 : CommonPoint.Point := ⟨1989, 3252, 1000⟩
kernel_matrix step2CommonGroup15_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope15.sourceIndex step2CommonScope15_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope15.sourceIndex step2CommonScope15_valid a))) step2CommonPoint15 = true)
kernel_matrix step2CommonGroup15_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope15.neighborIndex step2CommonScope15_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope15.neighborIndex step2CommonScope15_valid b))) step2CommonPoint15 = true)
def step2CommonGroup15 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope15 step2CommonScope15_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint15
  (fun a => step2CommonGroup15_sources a 0) (fun b => step2CommonGroup15_neighbors b 0)

def step2CommonScope16 : Scope := ⟨5, 6, 51, 8⟩
theorem step2CommonScope16_valid : step2CommonScope16.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup16_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope16.sourceIndex step2CommonScope16_valid a))
    (step2CommonRawNeighbors (step2CommonScope16.neighborIndex step2CommonScope16_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope16.sourceIndex step2CommonScope16_valid a))
      (step2CommonNeighborAngles (step2CommonScope16.neighborIndex step2CommonScope16_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup16 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope16 step2CommonScope16_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup16_checked

def step2CommonScope17 : Scope := ⟨11, 6, 51, 4⟩
theorem step2CommonScope17_valid : step2CommonScope17.Valid 47 59 := by decide +kernel

def step2CommonPoint17 : CommonPoint.Point := ⟨2009, 3303, 1000⟩
kernel_matrix step2CommonGroup17_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope17.sourceIndex step2CommonScope17_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope17.sourceIndex step2CommonScope17_valid a))) step2CommonPoint17 = true)
kernel_matrix step2CommonGroup17_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope17.neighborIndex step2CommonScope17_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope17.neighborIndex step2CommonScope17_valid b))) step2CommonPoint17 = true)
def step2CommonGroup17 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope17 step2CommonScope17_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint17
  (fun a => step2CommonGroup17_sources a 0) (fun b => step2CommonGroup17_neighbors b 0)

def step2CommonScope18 : Scope := ⟨11, 6, 55, 4⟩
theorem step2CommonScope18_valid : step2CommonScope18.Valid 47 59 := by decide +kernel

def step2CommonPoint18 : CommonPoint.Point := ⟨19935, 33232, 10000⟩
kernel_matrix step2CommonGroup18_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope18.sourceIndex step2CommonScope18_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope18.sourceIndex step2CommonScope18_valid a))) step2CommonPoint18 = true)
kernel_matrix step2CommonGroup18_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope18.neighborIndex step2CommonScope18_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope18.neighborIndex step2CommonScope18_valid b))) step2CommonPoint18 = true)
def step2CommonGroup18 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope18 step2CommonScope18_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint18
  (fun a => step2CommonGroup18_sources a 0) (fun b => step2CommonGroup18_neighbors b 0)

def step2CommonScope19 : Scope := ⟨17, 3, 51, 8⟩
theorem step2CommonScope19_valid : step2CommonScope19.Valid 47 59 := by decide +kernel

def step2CommonPoint19 : CommonPoint.Point := ⟨249, 413, 125⟩
kernel_matrix step2CommonGroup19_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope19.sourceIndex step2CommonScope19_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope19.sourceIndex step2CommonScope19_valid a))) step2CommonPoint19 = true)
kernel_matrix step2CommonGroup19_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope19.neighborIndex step2CommonScope19_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope19.neighborIndex step2CommonScope19_valid b))) step2CommonPoint19 = true)
def step2CommonGroup19 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope19 step2CommonScope19_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint19
  (fun a => step2CommonGroup19_sources a 0) (fun b => step2CommonGroup19_neighbors b 0)

def step2CommonScope20 : Scope := ⟨20, 3, 51, 8⟩
theorem step2CommonScope20_valid : step2CommonScope20.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup20_checked : 3 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope20.sourceIndex step2CommonScope20_valid a))
    (step2CommonRawNeighbors (step2CommonScope20.neighborIndex step2CommonScope20_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope20.sourceIndex step2CommonScope20_valid a))
      (step2CommonNeighborAngles (step2CommonScope20.neighborIndex step2CommonScope20_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup20 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope20 step2CommonScope20_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup20_checked

def step2CommonScope21 : Scope := ⟨23, 6, 29, 15⟩
theorem step2CommonScope21_valid : step2CommonScope21.Valid 47 59 := by decide +kernel

def step2CommonPoint21 : CommonPoint.Point := ⟨2055, 3214, 1000⟩
kernel_matrix step2CommonGroup21_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope21.sourceIndex step2CommonScope21_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope21.sourceIndex step2CommonScope21_valid a))) step2CommonPoint21 = true)
kernel_matrix step2CommonGroup21_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope21.neighborIndex step2CommonScope21_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope21.neighborIndex step2CommonScope21_valid b))) step2CommonPoint21 = true)
def step2CommonGroup21 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope21 step2CommonScope21_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint21
  (fun a => step2CommonGroup21_sources a 0) (fun b => step2CommonGroup21_neighbors b 0)

def step2CommonScope22 : Scope := ⟨29, 3, 29, 15⟩
theorem step2CommonScope22_valid : step2CommonScope22.Valid 47 59 := by decide +kernel

def step2CommonPoint22 : CommonPoint.Point := ⟨2039, 3147, 1000⟩
kernel_matrix step2CommonGroup22_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope22.sourceIndex step2CommonScope22_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope22.sourceIndex step2CommonScope22_valid a))) step2CommonPoint22 = true)
kernel_matrix step2CommonGroup22_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope22.neighborIndex step2CommonScope22_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope22.neighborIndex step2CommonScope22_valid b))) step2CommonPoint22 = true)
def step2CommonGroup22 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope22 step2CommonScope22_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint22
  (fun a => step2CommonGroup22_sources a 0) (fun b => step2CommonGroup22_neighbors b 0)

def step2CommonScope23 : Scope := ⟨32, 3, 29, 7⟩
theorem step2CommonScope23_valid : step2CommonScope23.Valid 47 59 := by decide +kernel

def step2CommonPoint23 : CommonPoint.Point := ⟨2092, 3223, 1000⟩
kernel_matrix step2CommonGroup23_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope23.sourceIndex step2CommonScope23_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope23.sourceIndex step2CommonScope23_valid a))) step2CommonPoint23 = true)
kernel_matrix step2CommonGroup23_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope23.neighborIndex step2CommonScope23_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope23.neighborIndex step2CommonScope23_valid b))) step2CommonPoint23 = true)
def step2CommonGroup23 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope23 step2CommonScope23_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint23
  (fun a => step2CommonGroup23_sources a 0) (fun b => step2CommonGroup23_neighbors b 0)

def step2CommonScope24 : Scope := ⟨32, 3, 36, 8⟩
theorem step2CommonScope24_valid : step2CommonScope24.Valid 47 59 := by decide +kernel

def step2CommonPoint24 : CommonPoint.Point := ⟨254, 388, 125⟩
kernel_matrix step2CommonGroup24_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope24.sourceIndex step2CommonScope24_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope24.sourceIndex step2CommonScope24_valid a))) step2CommonPoint24 = true)
kernel_matrix step2CommonGroup24_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope24.neighborIndex step2CommonScope24_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope24.neighborIndex step2CommonScope24_valid b))) step2CommonPoint24 = true)
def step2CommonGroup24 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope24 step2CommonScope24_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint24
  (fun a => step2CommonGroup24_sources a 0) (fun b => step2CommonGroup24_neighbors b 0)

def step2CommonScope25 : Scope := ⟨35, 12, 29, 15⟩
theorem step2CommonScope25_valid : step2CommonScope25.Valid 47 59 := by decide +kernel

def step2CommonPoint25 : CommonPoint.Point := ⟨20467, 31511, 10000⟩
kernel_matrix step2CommonGroup25_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope25.sourceIndex step2CommonScope25_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope25.sourceIndex step2CommonScope25_valid a))) step2CommonPoint25 = true)
kernel_matrix step2CommonGroup25_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope25.neighborIndex step2CommonScope25_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope25.neighborIndex step2CommonScope25_valid b))) step2CommonPoint25 = true)
def step2CommonGroup25 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope25 step2CommonScope25_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint25
  (fun a => step2CommonGroup25_sources a 0) (fun b => step2CommonGroup25_neighbors b 0)

def step2CommonScope26 : Scope := ⟨23, 12, 44, 15⟩
theorem step2CommonScope26_valid : step2CommonScope26.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup26_checked : 12 × 15 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope26.sourceIndex step2CommonScope26_valid a))
    (step2CommonRawNeighbors (step2CommonScope26.neighborIndex step2CommonScope26_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope26.sourceIndex step2CommonScope26_valid a))
      (step2CommonNeighborAngles (step2CommonScope26.neighborIndex step2CommonScope26_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup26 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope26 step2CommonScope26_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup26_checked

def step2CommonScope27 : Scope := ⟨35, 6, 44, 7⟩
theorem step2CommonScope27_valid : step2CommonScope27.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup27_checked : 6 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope27.sourceIndex step2CommonScope27_valid a))
    (step2CommonRawNeighbors (step2CommonScope27.neighborIndex step2CommonScope27_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope27.sourceIndex step2CommonScope27_valid a))
      (step2CommonNeighborAngles (step2CommonScope27.neighborIndex step2CommonScope27_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup27 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope27 step2CommonScope27_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup27_checked

def step2CommonScope28 : Scope := ⟨41, 6, 44, 7⟩
theorem step2CommonScope28_valid : step2CommonScope28.Valid 47 59 := by decide +kernel

def step2CommonPoint28 : CommonPoint.Point := ⟨997, 1520, 500⟩
kernel_matrix step2CommonGroup28_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope28.sourceIndex step2CommonScope28_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope28.sourceIndex step2CommonScope28_valid a))) step2CommonPoint28 = true)
kernel_matrix step2CommonGroup28_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope28.neighborIndex step2CommonScope28_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope28.neighborIndex step2CommonScope28_valid b))) step2CommonPoint28 = true)
def step2CommonGroup28 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope28 step2CommonScope28_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint28
  (fun a => step2CommonGroup28_sources a 0) (fun b => step2CommonGroup28_neighbors b 0)

def step2CommonScope29 : Scope := ⟨35, 6, 51, 8⟩
theorem step2CommonScope29_valid : step2CommonScope29.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup29_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope29.sourceIndex step2CommonScope29_valid a))
    (step2CommonRawNeighbors (step2CommonScope29.neighborIndex step2CommonScope29_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope29.sourceIndex step2CommonScope29_valid a))
      (step2CommonNeighborAngles (step2CommonScope29.neighborIndex step2CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup29 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope29 step2CommonScope29_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup29_checked

def step2CommonScope30 : Scope := ⟨41, 3, 51, 8⟩
theorem step2CommonScope30_valid : step2CommonScope30.Valid 47 59 := by decide +kernel

kernel_matrix step2CommonGroup30_checked : 3 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step2CommonRawSources (step2CommonScope30.sourceIndex step2CommonScope30_valid a))
    (step2CommonRawNeighbors (step2CommonScope30.neighborIndex step2CommonScope30_valid b))
    (fanDirectionKey (step2CommonSourceAngles (step2CommonScope30.sourceIndex step2CommonScope30_valid a))
      (step2CommonNeighborAngles (step2CommonScope30.neighborIndex step2CommonScope30_valid b))) (fun key => (key + 128) % 256))
def step2CommonGroup30 : CheckedGroup step2Sources step2Neighbors := fallbackGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope30 step2CommonScope30_valid
  step2CommonSourceAngles step2CommonNeighborAngles
  step2CommonSourceAngles_exact step2CommonNeighborAngles_exact
  step2CommonGroup30_checked

def step2CommonScope31 : Scope := ⟨44, 3, 51, 8⟩
theorem step2CommonScope31_valid : step2CommonScope31.Valid 47 59 := by decide +kernel

def step2CommonPoint31 : CommonPoint.Point := ⟨1990, 3029, 1000⟩
kernel_matrix step2CommonGroup31_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step2CommonRawSources (step2CommonScope31.sourceIndex step2CommonScope31_valid a))
    (ownKeys (step2CommonSourceAngles (step2CommonScope31.sourceIndex step2CommonScope31_valid a))) step2CommonPoint31 = true)
kernel_matrix step2CommonGroup31_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step2CommonRawNeighbors (step2CommonScope31.neighborIndex step2CommonScope31_valid b))
    (ownKeys (step2CommonNeighborAngles (step2CommonScope31.neighborIndex step2CommonScope31_valid b))) step2CommonPoint31 = true)
def step2CommonGroup31 : CheckedGroup step2Sources step2Neighbors := pointGroup
  step2Sources step2Neighbors
  step2CommonRawSources step2CommonRawNeighbors
  step2CommonRawSources_exact step2CommonRawNeighbors_exact
  step2CommonNeighborUnblocked step2CommonScope31 step2CommonScope31_valid
  (fun i => ownKeys (step2CommonSourceAngles i))
  (fun j => ownKeys (step2CommonNeighborAngles j)) step2CommonPoint31
  (fun a => step2CommonGroup31_sources a 0) (fun b => step2CommonGroup31_neighbors b 0)

def step2CommonScopes : List Scope := [
  step2CommonScope0, step2CommonScope1, step2CommonScope2, step2CommonScope3, step2CommonScope4, step2CommonScope5, step2CommonScope6, step2CommonScope7, step2CommonScope8, step2CommonScope9, step2CommonScope10, step2CommonScope11, step2CommonScope12, step2CommonScope13, step2CommonScope14, step2CommonScope15, step2CommonScope16, step2CommonScope17, step2CommonScope18, step2CommonScope19, step2CommonScope20, step2CommonScope21, step2CommonScope22, step2CommonScope23, step2CommonScope24, step2CommonScope25, step2CommonScope26, step2CommonScope27, step2CommonScope28, step2CommonScope29, step2CommonScope30, step2CommonScope31]
def step2CommonGroups : List (CheckedGroup step2Sources step2Neighbors) := [
  step2CommonGroup0, step2CommonGroup1, step2CommonGroup2, step2CommonGroup3, step2CommonGroup4, step2CommonGroup5, step2CommonGroup6, step2CommonGroup7, step2CommonGroup8, step2CommonGroup9, step2CommonGroup10, step2CommonGroup11, step2CommonGroup12, step2CommonGroup13, step2CommonGroup14, step2CommonGroup15, step2CommonGroup16, step2CommonGroup17, step2CommonGroup18, step2CommonGroup19, step2CommonGroup20, step2CommonGroup21, step2CommonGroup22, step2CommonGroup23, step2CommonGroup24, step2CommonGroup25, step2CommonGroup26, step2CommonGroup27, step2CommonGroup28, step2CommonGroup29, step2CommonGroup30, step2CommonGroup31]
theorem step2CommonScopes_exact :
    step2CommonGroups.map CheckedGroup.scope = step2CommonScopes := rfl
kernel_matrix step2CommonCoverage : 47 × 59 => (fun i j =>
  ScopeCheck step2CommonScopes i.val j.val)
theorem step2_geometric_overlap (i : Fin 47) (j : Fin 59) :
    PairOverlaps (step2Sources i) (step2Neighbors j) :=
  groups_sound step2Sources step2Neighbors step2CommonGroups
    step2CommonScopes step2CommonScopes_exact step2CommonCoverage i j
#print axioms step2_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
