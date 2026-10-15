import Compact.Cases.C898.CachedPairs.Step07CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step7CommonScope0 : Scope := ⟨0, 12, 0, 8⟩
theorem step7CommonScope0_valid : step7CommonScope0.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup0_checked : 12 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope0.sourceIndex step7CommonScope0_valid a))
    (step7CommonRawNeighbors (step7CommonScope0.neighborIndex step7CommonScope0_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope0.sourceIndex step7CommonScope0_valid a))
      (step7CommonNeighborAngles (step7CommonScope0.neighborIndex step7CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup0 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope0 step7CommonScope0_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup0_checked

def step7CommonScope1 : Scope := ⟨0, 6, 8, 8⟩
theorem step7CommonScope1_valid : step7CommonScope1.Valid 49 64 := by decide +kernel

def step7CommonPoint1 : CommonPoint.Point := ⟨2937, 886, 1000⟩
kernel_matrix step7CommonGroup1_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope1.sourceIndex step7CommonScope1_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope1.sourceIndex step7CommonScope1_valid a))) step7CommonPoint1 = true)
kernel_matrix step7CommonGroup1_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope1.neighborIndex step7CommonScope1_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope1.neighborIndex step7CommonScope1_valid b))) step7CommonPoint1 = true)
def step7CommonGroup1 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope1 step7CommonScope1_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint1
  (fun a => step7CommonGroup1_sources a 0) (fun b => step7CommonGroup1_neighbors b 0)

def step7CommonScope2 : Scope := ⟨6, 6, 8, 4⟩
theorem step7CommonScope2_valid : step7CommonScope2.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup2_checked : 6 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope2.sourceIndex step7CommonScope2_valid a))
    (step7CommonRawNeighbors (step7CommonScope2.neighborIndex step7CommonScope2_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope2.sourceIndex step7CommonScope2_valid a))
      (step7CommonNeighborAngles (step7CommonScope2.neighborIndex step7CommonScope2_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup2 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope2 step7CommonScope2_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup2_checked

def step7CommonScope3 : Scope := ⟨6, 6, 12, 4⟩
theorem step7CommonScope3_valid : step7CommonScope3.Valid 49 64 := by decide +kernel

def step7CommonPoint3 : CommonPoint.Point := ⟨2877, 896, 1000⟩
kernel_matrix step7CommonGroup3_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope3.sourceIndex step7CommonScope3_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope3.sourceIndex step7CommonScope3_valid a))) step7CommonPoint3 = true)
kernel_matrix step7CommonGroup3_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope3.neighborIndex step7CommonScope3_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope3.neighborIndex step7CommonScope3_valid b))) step7CommonPoint3 = true)
def step7CommonGroup3 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope3 step7CommonScope3_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint3
  (fun a => step7CommonGroup3_sources a 0) (fun b => step7CommonGroup3_neighbors b 0)

def step7CommonScope4 : Scope := ⟨12, 6, 0, 8⟩
theorem step7CommonScope4_valid : step7CommonScope4.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup4_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope4.sourceIndex step7CommonScope4_valid a))
    (step7CommonRawNeighbors (step7CommonScope4.neighborIndex step7CommonScope4_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope4.sourceIndex step7CommonScope4_valid a))
      (step7CommonNeighborAngles (step7CommonScope4.neighborIndex step7CommonScope4_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup4 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope4 step7CommonScope4_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup4_checked

def step7CommonScope5 : Scope := ⟨12, 6, 8, 4⟩
theorem step7CommonScope5_valid : step7CommonScope5.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup5_checked : 6 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope5.sourceIndex step7CommonScope5_valid a))
    (step7CommonRawNeighbors (step7CommonScope5.neighborIndex step7CommonScope5_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope5.sourceIndex step7CommonScope5_valid a))
      (step7CommonNeighborAngles (step7CommonScope5.neighborIndex step7CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup5 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope5 step7CommonScope5_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup5_checked

def step7CommonScope6 : Scope := ⟨12, 6, 12, 4⟩
theorem step7CommonScope6_valid : step7CommonScope6.Valid 49 64 := by decide +kernel

def step7CommonPoint6 : CommonPoint.Point := ⟨1437, 451, 500⟩
kernel_matrix step7CommonGroup6_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope6.sourceIndex step7CommonScope6_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope6.sourceIndex step7CommonScope6_valid a))) step7CommonPoint6 = true)
kernel_matrix step7CommonGroup6_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope6.neighborIndex step7CommonScope6_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope6.neighborIndex step7CommonScope6_valid b))) step7CommonPoint6 = true)
def step7CommonGroup6 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope6 step7CommonScope6_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint6
  (fun a => step7CommonGroup6_sources a 0) (fun b => step7CommonGroup6_neighbors b 0)

def step7CommonScope7 : Scope := ⟨18, 6, 0, 16⟩
theorem step7CommonScope7_valid : step7CommonScope7.Valid 49 64 := by decide +kernel

def step7CommonPoint7 : CommonPoint.Point := ⟨3033, 786, 1000⟩
kernel_matrix step7CommonGroup7_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope7.sourceIndex step7CommonScope7_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope7.sourceIndex step7CommonScope7_valid a))) step7CommonPoint7 = true)
kernel_matrix step7CommonGroup7_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope7.neighborIndex step7CommonScope7_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope7.neighborIndex step7CommonScope7_valid b))) step7CommonPoint7 = true)
def step7CommonGroup7 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope7 step7CommonScope7_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint7
  (fun a => step7CommonGroup7_sources a 0) (fun b => step7CommonGroup7_neighbors b 0)

def step7CommonScope8 : Scope := ⟨24, 12, 0, 8⟩
theorem step7CommonScope8_valid : step7CommonScope8.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup8_checked : 12 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope8.sourceIndex step7CommonScope8_valid a))
    (step7CommonRawNeighbors (step7CommonScope8.neighborIndex step7CommonScope8_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope8.sourceIndex step7CommonScope8_valid a))
      (step7CommonNeighborAngles (step7CommonScope8.neighborIndex step7CommonScope8_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup8 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope8 step7CommonScope8_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup8_checked

def step7CommonScope9 : Scope := ⟨36, 13, 0, 4⟩
theorem step7CommonScope9_valid : step7CommonScope9.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup9_checked : 13 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope9.sourceIndex step7CommonScope9_valid a))
    (step7CommonRawNeighbors (step7CommonScope9.neighborIndex step7CommonScope9_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope9.sourceIndex step7CommonScope9_valid a))
      (step7CommonNeighborAngles (step7CommonScope9.neighborIndex step7CommonScope9_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup9 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope9 step7CommonScope9_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup9_checked

def step7CommonScope10 : Scope := ⟨36, 13, 4, 4⟩
theorem step7CommonScope10_valid : step7CommonScope10.Valid 49 64 := by decide +kernel

def step7CommonPoint10 : CommonPoint.Point := ⟨2974, 935, 1000⟩
kernel_matrix step7CommonGroup10_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope10.sourceIndex step7CommonScope10_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope10.sourceIndex step7CommonScope10_valid a))) step7CommonPoint10 = true)
kernel_matrix step7CommonGroup10_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope10.neighborIndex step7CommonScope10_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope10.neighborIndex step7CommonScope10_valid b))) step7CommonPoint10 = true)
def step7CommonGroup10 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope10 step7CommonScope10_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint10
  (fun a => step7CommonGroup10_sources a 0) (fun b => step7CommonGroup10_neighbors b 0)

def step7CommonScope11 : Scope := ⟨24, 25, 8, 8⟩
theorem step7CommonScope11_valid : step7CommonScope11.Valid 49 64 := by decide +kernel

def step7CommonPoint11 : CommonPoint.Point := ⟨2925, 934, 1000⟩
kernel_matrix step7CommonGroup11_sources : 25 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope11.sourceIndex step7CommonScope11_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope11.sourceIndex step7CommonScope11_valid a))) step7CommonPoint11 = true)
kernel_matrix step7CommonGroup11_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope11.neighborIndex step7CommonScope11_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope11.neighborIndex step7CommonScope11_valid b))) step7CommonPoint11 = true)
def step7CommonGroup11 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope11 step7CommonScope11_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint11
  (fun a => step7CommonGroup11_sources a 0) (fun b => step7CommonGroup11_neighbors b 0)

def step7CommonScope12 : Scope := ⟨0, 49, 16, 16⟩
theorem step7CommonScope12_valid : step7CommonScope12.Valid 49 64 := by decide +kernel

def step7CommonPoint12 : CommonPoint.Point := ⟨2860, 859, 1000⟩
kernel_matrix step7CommonGroup12_sources : 49 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope12.sourceIndex step7CommonScope12_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope12.sourceIndex step7CommonScope12_valid a))) step7CommonPoint12 = true)
kernel_matrix step7CommonGroup12_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope12.neighborIndex step7CommonScope12_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope12.neighborIndex step7CommonScope12_valid b))) step7CommonPoint12 = true)
def step7CommonGroup12 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope12 step7CommonScope12_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint12
  (fun a => step7CommonGroup12_sources a 0) (fun b => step7CommonGroup12_neighbors b 0)

def step7CommonScope13 : Scope := ⟨0, 12, 32, 16⟩
theorem step7CommonScope13_valid : step7CommonScope13.Valid 49 64 := by decide +kernel

def step7CommonPoint13 : CommonPoint.Point := ⟨2927, 829, 1000⟩
kernel_matrix step7CommonGroup13_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope13.sourceIndex step7CommonScope13_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope13.sourceIndex step7CommonScope13_valid a))) step7CommonPoint13 = true)
kernel_matrix step7CommonGroup13_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope13.neighborIndex step7CommonScope13_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope13.neighborIndex step7CommonScope13_valid b))) step7CommonPoint13 = true)
def step7CommonGroup13 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope13 step7CommonScope13_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint13
  (fun a => step7CommonGroup13_sources a 0) (fun b => step7CommonGroup13_neighbors b 0)

def step7CommonScope14 : Scope := ⟨12, 12, 32, 8⟩
theorem step7CommonScope14_valid : step7CommonScope14.Valid 49 64 := by decide +kernel

def step7CommonPoint14 : CommonPoint.Point := ⟨2881, 837, 1000⟩
kernel_matrix step7CommonGroup14_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope14.sourceIndex step7CommonScope14_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope14.sourceIndex step7CommonScope14_valid a))) step7CommonPoint14 = true)
kernel_matrix step7CommonGroup14_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope14.neighborIndex step7CommonScope14_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope14.neighborIndex step7CommonScope14_valid b))) step7CommonPoint14 = true)
def step7CommonGroup14 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope14 step7CommonScope14_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint14
  (fun a => step7CommonGroup14_sources a 0) (fun b => step7CommonGroup14_neighbors b 0)

def step7CommonScope15 : Scope := ⟨12, 6, 40, 8⟩
theorem step7CommonScope15_valid : step7CommonScope15.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup15_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope15.sourceIndex step7CommonScope15_valid a))
    (step7CommonRawNeighbors (step7CommonScope15.neighborIndex step7CommonScope15_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope15.sourceIndex step7CommonScope15_valid a))
      (step7CommonNeighborAngles (step7CommonScope15.neighborIndex step7CommonScope15_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup15 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope15 step7CommonScope15_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup15_checked

def step7CommonScope16 : Scope := ⟨18, 6, 40, 8⟩
theorem step7CommonScope16_valid : step7CommonScope16.Valid 49 64 := by decide +kernel

def step7CommonPoint16 : CommonPoint.Point := ⟨2949, 782, 1000⟩
kernel_matrix step7CommonGroup16_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope16.sourceIndex step7CommonScope16_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope16.sourceIndex step7CommonScope16_valid a))) step7CommonPoint16 = true)
kernel_matrix step7CommonGroup16_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope16.neighborIndex step7CommonScope16_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope16.neighborIndex step7CommonScope16_valid b))) step7CommonPoint16 = true)
def step7CommonGroup16 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope16 step7CommonScope16_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint16
  (fun a => step7CommonGroup16_sources a 0) (fun b => step7CommonGroup16_neighbors b 0)

def step7CommonScope17 : Scope := ⟨0, 6, 48, 8⟩
theorem step7CommonScope17_valid : step7CommonScope17.Valid 49 64 := by decide +kernel

def step7CommonPoint17 : CommonPoint.Point := ⟨1487, 397, 500⟩
kernel_matrix step7CommonGroup17_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope17.sourceIndex step7CommonScope17_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope17.sourceIndex step7CommonScope17_valid a))) step7CommonPoint17 = true)
kernel_matrix step7CommonGroup17_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope17.neighborIndex step7CommonScope17_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope17.neighborIndex step7CommonScope17_valid b))) step7CommonPoint17 = true)
def step7CommonGroup17 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope17 step7CommonScope17_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint17
  (fun a => step7CommonGroup17_sources a 0) (fun b => step7CommonGroup17_neighbors b 0)

def step7CommonScope18 : Scope := ⟨6, 6, 48, 8⟩
theorem step7CommonScope18_valid : step7CommonScope18.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup18_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope18.sourceIndex step7CommonScope18_valid a))
    (step7CommonRawNeighbors (step7CommonScope18.neighborIndex step7CommonScope18_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope18.sourceIndex step7CommonScope18_valid a))
      (step7CommonNeighborAngles (step7CommonScope18.neighborIndex step7CommonScope18_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup18 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope18 step7CommonScope18_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup18_checked

def step7CommonScope19 : Scope := ⟨0, 12, 56, 8⟩
theorem step7CommonScope19_valid : step7CommonScope19.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup19_checked : 12 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope19.sourceIndex step7CommonScope19_valid a))
    (step7CommonRawNeighbors (step7CommonScope19.neighborIndex step7CommonScope19_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope19.sourceIndex step7CommonScope19_valid a))
      (step7CommonNeighborAngles (step7CommonScope19.neighborIndex step7CommonScope19_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup19 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope19 step7CommonScope19_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup19_checked

def step7CommonScope20 : Scope := ⟨12, 6, 48, 16⟩
theorem step7CommonScope20_valid : step7CommonScope20.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup20_checked : 6 × 16 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope20.sourceIndex step7CommonScope20_valid a))
    (step7CommonRawNeighbors (step7CommonScope20.neighborIndex step7CommonScope20_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope20.sourceIndex step7CommonScope20_valid a))
      (step7CommonNeighborAngles (step7CommonScope20.neighborIndex step7CommonScope20_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup20 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope20 step7CommonScope20_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup20_checked

def step7CommonScope21 : Scope := ⟨18, 6, 48, 16⟩
theorem step7CommonScope21_valid : step7CommonScope21.Valid 49 64 := by decide +kernel

def step7CommonPoint21 : CommonPoint.Point := ⟨1514, 393, 500⟩
kernel_matrix step7CommonGroup21_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope21.sourceIndex step7CommonScope21_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope21.sourceIndex step7CommonScope21_valid a))) step7CommonPoint21 = true)
kernel_matrix step7CommonGroup21_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope21.neighborIndex step7CommonScope21_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope21.neighborIndex step7CommonScope21_valid b))) step7CommonPoint21 = true)
def step7CommonGroup21 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope21 step7CommonScope21_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint21
  (fun a => step7CommonGroup21_sources a 0) (fun b => step7CommonGroup21_neighbors b 0)

def step7CommonScope22 : Scope := ⟨24, 12, 32, 8⟩
theorem step7CommonScope22_valid : step7CommonScope22.Valid 49 64 := by decide +kernel

def step7CommonPoint22 : CommonPoint.Point := ⟨2911, 902, 1000⟩
kernel_matrix step7CommonGroup22_sources : 12 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope22.sourceIndex step7CommonScope22_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope22.sourceIndex step7CommonScope22_valid a))) step7CommonPoint22 = true)
kernel_matrix step7CommonGroup22_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope22.neighborIndex step7CommonScope22_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope22.neighborIndex step7CommonScope22_valid b))) step7CommonPoint22 = true)
def step7CommonGroup22 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope22 step7CommonScope22_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint22
  (fun a => step7CommonGroup22_sources a 0) (fun b => step7CommonGroup22_neighbors b 0)

def step7CommonScope23 : Scope := ⟨24, 6, 40, 8⟩
theorem step7CommonScope23_valid : step7CommonScope23.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup23_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope23.sourceIndex step7CommonScope23_valid a))
    (step7CommonRawNeighbors (step7CommonScope23.neighborIndex step7CommonScope23_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope23.sourceIndex step7CommonScope23_valid a))
      (step7CommonNeighborAngles (step7CommonScope23.neighborIndex step7CommonScope23_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup23 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope23 step7CommonScope23_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup23_checked

def step7CommonScope24 : Scope := ⟨30, 6, 40, 8⟩
theorem step7CommonScope24_valid : step7CommonScope24.Valid 49 64 := by decide +kernel

def step7CommonPoint24 : CommonPoint.Point := ⟨2954, 911, 1000⟩
kernel_matrix step7CommonGroup24_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope24.sourceIndex step7CommonScope24_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope24.sourceIndex step7CommonScope24_valid a))) step7CommonPoint24 = true)
kernel_matrix step7CommonGroup24_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope24.neighborIndex step7CommonScope24_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope24.neighborIndex step7CommonScope24_valid b))) step7CommonPoint24 = true)
def step7CommonGroup24 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope24 step7CommonScope24_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint24
  (fun a => step7CommonGroup24_sources a 0) (fun b => step7CommonGroup24_neighbors b 0)

def step7CommonScope25 : Scope := ⟨36, 13, 32, 16⟩
theorem step7CommonScope25_valid : step7CommonScope25.Valid 49 64 := by decide +kernel

def step7CommonPoint25 : CommonPoint.Point := ⟨2926, 795, 1000⟩
kernel_matrix step7CommonGroup25_sources : 13 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope25.sourceIndex step7CommonScope25_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope25.sourceIndex step7CommonScope25_valid a))) step7CommonPoint25 = true)
kernel_matrix step7CommonGroup25_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope25.neighborIndex step7CommonScope25_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope25.neighborIndex step7CommonScope25_valid b))) step7CommonPoint25 = true)
def step7CommonGroup25 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope25 step7CommonScope25_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint25
  (fun a => step7CommonGroup25_sources a 0) (fun b => step7CommonGroup25_neighbors b 0)

def step7CommonScope26 : Scope := ⟨24, 12, 48, 16⟩
theorem step7CommonScope26_valid : step7CommonScope26.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup26_checked : 12 × 16 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope26.sourceIndex step7CommonScope26_valid a))
    (step7CommonRawNeighbors (step7CommonScope26.neighborIndex step7CommonScope26_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope26.sourceIndex step7CommonScope26_valid a))
      (step7CommonNeighborAngles (step7CommonScope26.neighborIndex step7CommonScope26_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup26 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope26 step7CommonScope26_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup26_checked

def step7CommonScope27 : Scope := ⟨36, 6, 48, 8⟩
theorem step7CommonScope27_valid : step7CommonScope27.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup27_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope27.sourceIndex step7CommonScope27_valid a))
    (step7CommonRawNeighbors (step7CommonScope27.neighborIndex step7CommonScope27_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope27.sourceIndex step7CommonScope27_valid a))
      (step7CommonNeighborAngles (step7CommonScope27.neighborIndex step7CommonScope27_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup27 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope27 step7CommonScope27_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup27_checked

def step7CommonScope28 : Scope := ⟨42, 7, 48, 8⟩
theorem step7CommonScope28_valid : step7CommonScope28.Valid 49 64 := by decide +kernel

def step7CommonPoint28 : CommonPoint.Point := ⟨2994, 947, 1000⟩
kernel_matrix step7CommonGroup28_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step7CommonRawSources (step7CommonScope28.sourceIndex step7CommonScope28_valid a))
    (ownKeys (step7CommonSourceAngles (step7CommonScope28.sourceIndex step7CommonScope28_valid a))) step7CommonPoint28 = true)
kernel_matrix step7CommonGroup28_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step7CommonRawNeighbors (step7CommonScope28.neighborIndex step7CommonScope28_valid b))
    (ownKeys (step7CommonNeighborAngles (step7CommonScope28.neighborIndex step7CommonScope28_valid b))) step7CommonPoint28 = true)
def step7CommonGroup28 : CheckedGroup step7Sources step7Neighbors := pointGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope28 step7CommonScope28_valid
  (fun i => ownKeys (step7CommonSourceAngles i))
  (fun j => ownKeys (step7CommonNeighborAngles j)) step7CommonPoint28
  (fun a => step7CommonGroup28_sources a 0) (fun b => step7CommonGroup28_neighbors b 0)

def step7CommonScope29 : Scope := ⟨36, 13, 56, 8⟩
theorem step7CommonScope29_valid : step7CommonScope29.Valid 49 64 := by decide +kernel

kernel_matrix step7CommonGroup29_checked : 13 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step7CommonRawSources (step7CommonScope29.sourceIndex step7CommonScope29_valid a))
    (step7CommonRawNeighbors (step7CommonScope29.neighborIndex step7CommonScope29_valid b))
    (fanDirectionKey (step7CommonSourceAngles (step7CommonScope29.sourceIndex step7CommonScope29_valid a))
      (step7CommonNeighborAngles (step7CommonScope29.neighborIndex step7CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step7CommonGroup29 : CheckedGroup step7Sources step7Neighbors := fallbackGroup
  step7Sources step7Neighbors
  step7CommonRawSources step7CommonRawNeighbors
  step7CommonRawSources_exact step7CommonRawNeighbors_exact
  step7CommonNeighborUnblocked step7CommonScope29 step7CommonScope29_valid
  step7CommonSourceAngles step7CommonNeighborAngles
  step7CommonSourceAngles_exact step7CommonNeighborAngles_exact
  step7CommonGroup29_checked

def step7CommonScopes : List Scope := [
  step7CommonScope0, step7CommonScope1, step7CommonScope2, step7CommonScope3, step7CommonScope4, step7CommonScope5, step7CommonScope6, step7CommonScope7, step7CommonScope8, step7CommonScope9, step7CommonScope10, step7CommonScope11, step7CommonScope12, step7CommonScope13, step7CommonScope14, step7CommonScope15, step7CommonScope16, step7CommonScope17, step7CommonScope18, step7CommonScope19, step7CommonScope20, step7CommonScope21, step7CommonScope22, step7CommonScope23, step7CommonScope24, step7CommonScope25, step7CommonScope26, step7CommonScope27, step7CommonScope28, step7CommonScope29]
def step7CommonGroups : List (CheckedGroup step7Sources step7Neighbors) := [
  step7CommonGroup0, step7CommonGroup1, step7CommonGroup2, step7CommonGroup3, step7CommonGroup4, step7CommonGroup5, step7CommonGroup6, step7CommonGroup7, step7CommonGroup8, step7CommonGroup9, step7CommonGroup10, step7CommonGroup11, step7CommonGroup12, step7CommonGroup13, step7CommonGroup14, step7CommonGroup15, step7CommonGroup16, step7CommonGroup17, step7CommonGroup18, step7CommonGroup19, step7CommonGroup20, step7CommonGroup21, step7CommonGroup22, step7CommonGroup23, step7CommonGroup24, step7CommonGroup25, step7CommonGroup26, step7CommonGroup27, step7CommonGroup28, step7CommonGroup29]
theorem step7CommonScopes_exact :
    step7CommonGroups.map CheckedGroup.scope = step7CommonScopes := rfl
kernel_matrix step7CommonCoverage : 49 × 64 => (fun i j =>
  ScopeCheck step7CommonScopes i.val j.val)
theorem step7_geometric_overlap (i : Fin 49) (j : Fin 64) :
    PairOverlaps (step7Sources i) (step7Neighbors j) :=
  groups_sound step7Sources step7Neighbors step7CommonGroups
    step7CommonScopes step7CommonScopes_exact step7CommonCoverage i j
#print axioms step7_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
