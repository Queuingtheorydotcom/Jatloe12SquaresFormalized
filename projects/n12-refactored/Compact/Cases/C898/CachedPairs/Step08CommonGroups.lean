import Compact.Cases.C898.CachedPairs.Step08CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step8CommonScope0 : Scope := ⟨0, 8, 0, 8⟩
theorem step8CommonScope0_valid : step8CommonScope0.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup0_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope0.sourceIndex step8CommonScope0_valid a))
    (step8CommonRawNeighbors (step8CommonScope0.neighborIndex step8CommonScope0_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope0.sourceIndex step8CommonScope0_valid a))
      (step8CommonNeighborAngles (step8CommonScope0.neighborIndex step8CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup0 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope0 step8CommonScope0_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup0_checked

def step8CommonScope1 : Scope := ⟨8, 8, 0, 4⟩
theorem step8CommonScope1_valid : step8CommonScope1.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup1_checked : 8 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope1.sourceIndex step8CommonScope1_valid a))
    (step8CommonRawNeighbors (step8CommonScope1.neighborIndex step8CommonScope1_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope1.sourceIndex step8CommonScope1_valid a))
      (step8CommonNeighborAngles (step8CommonScope1.neighborIndex step8CommonScope1_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup1 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope1 step8CommonScope1_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup1_checked

def step8CommonScope2 : Scope := ⟨8, 8, 4, 4⟩
theorem step8CommonScope2_valid : step8CommonScope2.Valid 64 64 := by decide +kernel

def step8CommonPoint2 : CommonPoint.Point := ⟨1075, 1031, 1000⟩
kernel_matrix step8CommonGroup2_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope2.sourceIndex step8CommonScope2_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope2.sourceIndex step8CommonScope2_valid a))) step8CommonPoint2 = true)
kernel_matrix step8CommonGroup2_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope2.neighborIndex step8CommonScope2_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope2.neighborIndex step8CommonScope2_valid b))) step8CommonPoint2 = true)
def step8CommonGroup2 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope2 step8CommonScope2_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint2
  (fun a => step8CommonGroup2_sources a 0) (fun b => step8CommonGroup2_neighbors b 0)

def step8CommonScope3 : Scope := ⟨16, 16, 0, 4⟩
theorem step8CommonScope3_valid : step8CommonScope3.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup3_checked : 16 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope3.sourceIndex step8CommonScope3_valid a))
    (step8CommonRawNeighbors (step8CommonScope3.neighborIndex step8CommonScope3_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope3.sourceIndex step8CommonScope3_valid a))
      (step8CommonNeighborAngles (step8CommonScope3.neighborIndex step8CommonScope3_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup3 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope3 step8CommonScope3_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup3_checked

def step8CommonScope4 : Scope := ⟨16, 16, 4, 4⟩
theorem step8CommonScope4_valid : step8CommonScope4.Valid 64 64 := by decide +kernel

def step8CommonPoint4 : CommonPoint.Point := ⟨1073, 1036, 1000⟩
kernel_matrix step8CommonGroup4_sources : 16 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope4.sourceIndex step8CommonScope4_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope4.sourceIndex step8CommonScope4_valid a))) step8CommonPoint4 = true)
kernel_matrix step8CommonGroup4_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope4.neighborIndex step8CommonScope4_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope4.neighborIndex step8CommonScope4_valid b))) step8CommonPoint4 = true)
def step8CommonGroup4 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope4 step8CommonScope4_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint4
  (fun a => step8CommonGroup4_sources a 0) (fun b => step8CommonGroup4_neighbors b 0)

def step8CommonScope5 : Scope := ⟨32, 8, 0, 8⟩
theorem step8CommonScope5_valid : step8CommonScope5.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup5_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope5.sourceIndex step8CommonScope5_valid a))
    (step8CommonRawNeighbors (step8CommonScope5.neighborIndex step8CommonScope5_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope5.sourceIndex step8CommonScope5_valid a))
      (step8CommonNeighborAngles (step8CommonScope5.neighborIndex step8CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup5 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope5 step8CommonScope5_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup5_checked

def step8CommonScope6 : Scope := ⟨40, 8, 0, 8⟩
theorem step8CommonScope6_valid : step8CommonScope6.Valid 64 64 := by decide +kernel

def step8CommonPoint6 : CommonPoint.Point := ⟨498, 511, 500⟩
kernel_matrix step8CommonGroup6_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope6.sourceIndex step8CommonScope6_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope6.sourceIndex step8CommonScope6_valid a))) step8CommonPoint6 = true)
kernel_matrix step8CommonGroup6_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope6.neighborIndex step8CommonScope6_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope6.neighborIndex step8CommonScope6_valid b))) step8CommonPoint6 = true)
def step8CommonGroup6 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope6 step8CommonScope6_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint6
  (fun a => step8CommonGroup6_sources a 0) (fun b => step8CommonGroup6_neighbors b 0)

def step8CommonScope7 : Scope := ⟨48, 8, 0, 8⟩
theorem step8CommonScope7_valid : step8CommonScope7.Valid 64 64 := by decide +kernel

def step8CommonPoint7 : CommonPoint.Point := ⟨994, 1045, 1000⟩
kernel_matrix step8CommonGroup7_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope7.sourceIndex step8CommonScope7_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope7.sourceIndex step8CommonScope7_valid a))) step8CommonPoint7 = true)
kernel_matrix step8CommonGroup7_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope7.neighborIndex step8CommonScope7_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope7.neighborIndex step8CommonScope7_valid b))) step8CommonPoint7 = true)
def step8CommonGroup7 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope7 step8CommonScope7_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint7
  (fun a => step8CommonGroup7_sources a 0) (fun b => step8CommonGroup7_neighbors b 0)

def step8CommonScope8 : Scope := ⟨56, 4, 0, 8⟩
theorem step8CommonScope8_valid : step8CommonScope8.Valid 64 64 := by decide +kernel

def step8CommonPoint8 : CommonPoint.Point := ⟨995, 1037, 1000⟩
kernel_matrix step8CommonGroup8_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope8.sourceIndex step8CommonScope8_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope8.sourceIndex step8CommonScope8_valid a))) step8CommonPoint8 = true)
kernel_matrix step8CommonGroup8_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope8.neighborIndex step8CommonScope8_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope8.neighborIndex step8CommonScope8_valid b))) step8CommonPoint8 = true)
def step8CommonGroup8 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope8 step8CommonScope8_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint8
  (fun a => step8CommonGroup8_sources a 0) (fun b => step8CommonGroup8_neighbors b 0)

def step8CommonScope9 : Scope := ⟨60, 4, 0, 8⟩
theorem step8CommonScope9_valid : step8CommonScope9.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup9_checked : 4 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope9.sourceIndex step8CommonScope9_valid a))
    (step8CommonRawNeighbors (step8CommonScope9.neighborIndex step8CommonScope9_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope9.sourceIndex step8CommonScope9_valid a))
      (step8CommonNeighborAngles (step8CommonScope9.neighborIndex step8CommonScope9_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup9 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope9 step8CommonScope9_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup9_checked

def step8CommonScope10 : Scope := ⟨0, 64, 8, 8⟩
theorem step8CommonScope10_valid : step8CommonScope10.Valid 64 64 := by decide +kernel

def step8CommonPoint10 : CommonPoint.Point := ⟨509, 505, 500⟩
kernel_matrix step8CommonGroup10_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope10.sourceIndex step8CommonScope10_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope10.sourceIndex step8CommonScope10_valid a))) step8CommonPoint10 = true)
kernel_matrix step8CommonGroup10_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope10.neighborIndex step8CommonScope10_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope10.neighborIndex step8CommonScope10_valid b))) step8CommonPoint10 = true)
def step8CommonGroup10 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope10 step8CommonScope10_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint10
  (fun a => step8CommonGroup10_sources a 0) (fun b => step8CommonGroup10_neighbors b 0)

def step8CommonScope11 : Scope := ⟨0, 64, 16, 16⟩
theorem step8CommonScope11_valid : step8CommonScope11.Valid 64 64 := by decide +kernel

def step8CommonPoint11 : CommonPoint.Point := ⟨1023, 991, 1000⟩
kernel_matrix step8CommonGroup11_sources : 64 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope11.sourceIndex step8CommonScope11_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope11.sourceIndex step8CommonScope11_valid a))) step8CommonPoint11 = true)
kernel_matrix step8CommonGroup11_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope11.neighborIndex step8CommonScope11_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope11.neighborIndex step8CommonScope11_valid b))) step8CommonPoint11 = true)
def step8CommonGroup11 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope11 step8CommonScope11_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint11
  (fun a => step8CommonGroup11_sources a 0) (fun b => step8CommonGroup11_neighbors b 0)

def step8CommonScope12 : Scope := ⟨0, 8, 32, 16⟩
theorem step8CommonScope12_valid : step8CommonScope12.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup12_checked : 8 × 16 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope12.sourceIndex step8CommonScope12_valid a))
    (step8CommonRawNeighbors (step8CommonScope12.neighborIndex step8CommonScope12_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope12.sourceIndex step8CommonScope12_valid a))
      (step8CommonNeighborAngles (step8CommonScope12.neighborIndex step8CommonScope12_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup12 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope12 step8CommonScope12_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup12_checked

def step8CommonScope13 : Scope := ⟨8, 8, 32, 16⟩
theorem step8CommonScope13_valid : step8CommonScope13.Valid 64 64 := by decide +kernel

def step8CommonPoint13 : CommonPoint.Point := ⟨967, 988, 1000⟩
kernel_matrix step8CommonGroup13_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope13.sourceIndex step8CommonScope13_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope13.sourceIndex step8CommonScope13_valid a))) step8CommonPoint13 = true)
kernel_matrix step8CommonGroup13_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope13.neighborIndex step8CommonScope13_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope13.neighborIndex step8CommonScope13_valid b))) step8CommonPoint13 = true)
def step8CommonGroup13 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope13 step8CommonScope13_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint13
  (fun a => step8CommonGroup13_sources a 0) (fun b => step8CommonGroup13_neighbors b 0)

def step8CommonScope14 : Scope := ⟨16, 16, 32, 16⟩
theorem step8CommonScope14_valid : step8CommonScope14.Valid 64 64 := by decide +kernel

def step8CommonPoint14 : CommonPoint.Point := ⟨949, 939, 1000⟩
kernel_matrix step8CommonGroup14_sources : 16 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope14.sourceIndex step8CommonScope14_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope14.sourceIndex step8CommonScope14_valid a))) step8CommonPoint14 = true)
kernel_matrix step8CommonGroup14_neighbors : 16 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope14.neighborIndex step8CommonScope14_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope14.neighborIndex step8CommonScope14_valid b))) step8CommonPoint14 = true)
def step8CommonGroup14 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope14 step8CommonScope14_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint14
  (fun a => step8CommonGroup14_sources a 0) (fun b => step8CommonGroup14_neighbors b 0)

def step8CommonScope15 : Scope := ⟨0, 8, 48, 8⟩
theorem step8CommonScope15_valid : step8CommonScope15.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup15_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope15.sourceIndex step8CommonScope15_valid a))
    (step8CommonRawNeighbors (step8CommonScope15.neighborIndex step8CommonScope15_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope15.sourceIndex step8CommonScope15_valid a))
      (step8CommonNeighborAngles (step8CommonScope15.neighborIndex step8CommonScope15_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup15 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope15 step8CommonScope15_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup15_checked

def step8CommonScope16 : Scope := ⟨8, 8, 48, 8⟩
theorem step8CommonScope16_valid : step8CommonScope16.Valid 64 64 := by decide +kernel

def step8CommonPoint16 : CommonPoint.Point := ⟨966, 995, 1000⟩
kernel_matrix step8CommonGroup16_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope16.sourceIndex step8CommonScope16_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope16.sourceIndex step8CommonScope16_valid a))) step8CommonPoint16 = true)
kernel_matrix step8CommonGroup16_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope16.neighborIndex step8CommonScope16_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope16.neighborIndex step8CommonScope16_valid b))) step8CommonPoint16 = true)
def step8CommonGroup16 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope16 step8CommonScope16_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint16
  (fun a => step8CommonGroup16_sources a 0) (fun b => step8CommonGroup16_neighbors b 0)

def step8CommonScope17 : Scope := ⟨0, 8, 56, 8⟩
theorem step8CommonScope17_valid : step8CommonScope17.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup17_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope17.sourceIndex step8CommonScope17_valid a))
    (step8CommonRawNeighbors (step8CommonScope17.neighborIndex step8CommonScope17_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope17.sourceIndex step8CommonScope17_valid a))
      (step8CommonNeighborAngles (step8CommonScope17.neighborIndex step8CommonScope17_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup17 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope17 step8CommonScope17_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup17_checked

def step8CommonScope18 : Scope := ⟨8, 8, 56, 8⟩
theorem step8CommonScope18_valid : step8CommonScope18.Valid 64 64 := by decide +kernel

def step8CommonPoint18 : CommonPoint.Point := ⟨985, 1008, 1000⟩
kernel_matrix step8CommonGroup18_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope18.sourceIndex step8CommonScope18_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope18.sourceIndex step8CommonScope18_valid a))) step8CommonPoint18 = true)
kernel_matrix step8CommonGroup18_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope18.neighborIndex step8CommonScope18_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope18.neighborIndex step8CommonScope18_valid b))) step8CommonPoint18 = true)
def step8CommonGroup18 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope18 step8CommonScope18_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint18
  (fun a => step8CommonGroup18_sources a 0) (fun b => step8CommonGroup18_neighbors b 0)

def step8CommonScope19 : Scope := ⟨16, 8, 48, 8⟩
theorem step8CommonScope19_valid : step8CommonScope19.Valid 64 64 := by decide +kernel

def step8CommonPoint19 : CommonPoint.Point := ⟨971, 991, 1000⟩
kernel_matrix step8CommonGroup19_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope19.sourceIndex step8CommonScope19_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope19.sourceIndex step8CommonScope19_valid a))) step8CommonPoint19 = true)
kernel_matrix step8CommonGroup19_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope19.neighborIndex step8CommonScope19_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope19.neighborIndex step8CommonScope19_valid b))) step8CommonPoint19 = true)
def step8CommonGroup19 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope19 step8CommonScope19_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint19
  (fun a => step8CommonGroup19_sources a 0) (fun b => step8CommonGroup19_neighbors b 0)

def step8CommonScope20 : Scope := ⟨24, 8, 48, 4⟩
theorem step8CommonScope20_valid : step8CommonScope20.Valid 64 64 := by decide +kernel

def step8CommonPoint20 : CommonPoint.Point := ⟨963, 967, 1000⟩
kernel_matrix step8CommonGroup20_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope20.sourceIndex step8CommonScope20_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope20.sourceIndex step8CommonScope20_valid a))) step8CommonPoint20 = true)
kernel_matrix step8CommonGroup20_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope20.neighborIndex step8CommonScope20_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope20.neighborIndex step8CommonScope20_valid b))) step8CommonPoint20 = true)
def step8CommonGroup20 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope20 step8CommonScope20_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint20
  (fun a => step8CommonGroup20_sources a 0) (fun b => step8CommonGroup20_neighbors b 0)

def step8CommonScope21 : Scope := ⟨24, 8, 52, 4⟩
theorem step8CommonScope21_valid : step8CommonScope21.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup21_checked : 8 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope21.sourceIndex step8CommonScope21_valid a))
    (step8CommonRawNeighbors (step8CommonScope21.neighborIndex step8CommonScope21_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope21.sourceIndex step8CommonScope21_valid a))
      (step8CommonNeighborAngles (step8CommonScope21.neighborIndex step8CommonScope21_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup21 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope21 step8CommonScope21_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup21_checked

def step8CommonScope22 : Scope := ⟨16, 8, 56, 4⟩
theorem step8CommonScope22_valid : step8CommonScope22.Valid 64 64 := by decide +kernel

def step8CommonPoint22 : CommonPoint.Point := ⟨492, 501, 500⟩
kernel_matrix step8CommonGroup22_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope22.sourceIndex step8CommonScope22_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope22.sourceIndex step8CommonScope22_valid a))) step8CommonPoint22 = true)
kernel_matrix step8CommonGroup22_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope22.neighborIndex step8CommonScope22_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope22.neighborIndex step8CommonScope22_valid b))) step8CommonPoint22 = true)
def step8CommonGroup22 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope22 step8CommonScope22_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint22
  (fun a => step8CommonGroup22_sources a 0) (fun b => step8CommonGroup22_neighbors b 0)

def step8CommonScope23 : Scope := ⟨16, 8, 60, 4⟩
theorem step8CommonScope23_valid : step8CommonScope23.Valid 64 64 := by decide +kernel

def step8CommonPoint23 : CommonPoint.Point := ⟨495, 504, 500⟩
kernel_matrix step8CommonGroup23_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope23.sourceIndex step8CommonScope23_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope23.sourceIndex step8CommonScope23_valid a))) step8CommonPoint23 = true)
kernel_matrix step8CommonGroup23_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope23.neighborIndex step8CommonScope23_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope23.neighborIndex step8CommonScope23_valid b))) step8CommonPoint23 = true)
def step8CommonGroup23 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope23 step8CommonScope23_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint23
  (fun a => step8CommonGroup23_sources a 0) (fun b => step8CommonGroup23_neighbors b 0)

def step8CommonScope24 : Scope := ⟨24, 8, 56, 8⟩
theorem step8CommonScope24_valid : step8CommonScope24.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup24_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope24.sourceIndex step8CommonScope24_valid a))
    (step8CommonRawNeighbors (step8CommonScope24.neighborIndex step8CommonScope24_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope24.sourceIndex step8CommonScope24_valid a))
      (step8CommonNeighborAngles (step8CommonScope24.neighborIndex step8CommonScope24_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup24 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope24 step8CommonScope24_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup24_checked

def step8CommonScope25 : Scope := ⟨32, 32, 32, 8⟩
theorem step8CommonScope25_valid : step8CommonScope25.Valid 64 64 := by decide +kernel

def step8CommonPoint25 : CommonPoint.Point := ⟨9924, 10073, 10000⟩
kernel_matrix step8CommonGroup25_sources : 32 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope25.sourceIndex step8CommonScope25_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope25.sourceIndex step8CommonScope25_valid a))) step8CommonPoint25 = true)
kernel_matrix step8CommonGroup25_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope25.neighborIndex step8CommonScope25_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope25.neighborIndex step8CommonScope25_valid b))) step8CommonPoint25 = true)
def step8CommonGroup25 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope25 step8CommonScope25_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint25
  (fun a => step8CommonGroup25_sources a 0) (fun b => step8CommonGroup25_neighbors b 0)

def step8CommonScope26 : Scope := ⟨32, 16, 40, 8⟩
theorem step8CommonScope26_valid : step8CommonScope26.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup26_checked : 16 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope26.sourceIndex step8CommonScope26_valid a))
    (step8CommonRawNeighbors (step8CommonScope26.neighborIndex step8CommonScope26_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope26.sourceIndex step8CommonScope26_valid a))
      (step8CommonNeighborAngles (step8CommonScope26.neighborIndex step8CommonScope26_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup26 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope26 step8CommonScope26_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup26_checked

def step8CommonScope27 : Scope := ⟨48, 8, 40, 8⟩
theorem step8CommonScope27_valid : step8CommonScope27.Valid 64 64 := by decide +kernel

def step8CommonPoint27 : CommonPoint.Point := ⟨1000, 1087, 1000⟩
kernel_matrix step8CommonGroup27_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope27.sourceIndex step8CommonScope27_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope27.sourceIndex step8CommonScope27_valid a))) step8CommonPoint27 = true)
kernel_matrix step8CommonGroup27_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope27.neighborIndex step8CommonScope27_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope27.neighborIndex step8CommonScope27_valid b))) step8CommonPoint27 = true)
def step8CommonGroup27 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope27 step8CommonScope27_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint27
  (fun a => step8CommonGroup27_sources a 0) (fun b => step8CommonGroup27_neighbors b 0)

def step8CommonScope28 : Scope := ⟨56, 8, 40, 8⟩
theorem step8CommonScope28_valid : step8CommonScope28.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup28_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope28.sourceIndex step8CommonScope28_valid a))
    (step8CommonRawNeighbors (step8CommonScope28.neighborIndex step8CommonScope28_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope28.sourceIndex step8CommonScope28_valid a))
      (step8CommonNeighborAngles (step8CommonScope28.neighborIndex step8CommonScope28_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup28 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope28 step8CommonScope28_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup28_checked

def step8CommonScope29 : Scope := ⟨32, 8, 48, 8⟩
theorem step8CommonScope29_valid : step8CommonScope29.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup29_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope29.sourceIndex step8CommonScope29_valid a))
    (step8CommonRawNeighbors (step8CommonScope29.neighborIndex step8CommonScope29_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope29.sourceIndex step8CommonScope29_valid a))
      (step8CommonNeighborAngles (step8CommonScope29.neighborIndex step8CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup29 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope29 step8CommonScope29_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup29_checked

def step8CommonScope30 : Scope := ⟨40, 4, 48, 8⟩
theorem step8CommonScope30_valid : step8CommonScope30.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup30_checked : 4 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope30.sourceIndex step8CommonScope30_valid a))
    (step8CommonRawNeighbors (step8CommonScope30.neighborIndex step8CommonScope30_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope30.sourceIndex step8CommonScope30_valid a))
      (step8CommonNeighborAngles (step8CommonScope30.neighborIndex step8CommonScope30_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup30 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope30 step8CommonScope30_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup30_checked

def step8CommonScope31 : Scope := ⟨44, 4, 48, 8⟩
theorem step8CommonScope31_valid : step8CommonScope31.Valid 64 64 := by decide +kernel

def step8CommonPoint31 : CommonPoint.Point := ⟨973, 994, 1000⟩
kernel_matrix step8CommonGroup31_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope31.sourceIndex step8CommonScope31_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope31.sourceIndex step8CommonScope31_valid a))) step8CommonPoint31 = true)
kernel_matrix step8CommonGroup31_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope31.neighborIndex step8CommonScope31_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope31.neighborIndex step8CommonScope31_valid b))) step8CommonPoint31 = true)
def step8CommonGroup31 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope31 step8CommonScope31_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint31
  (fun a => step8CommonGroup31_sources a 0) (fun b => step8CommonGroup31_neighbors b 0)

def step8CommonScope32 : Scope := ⟨32, 8, 56, 8⟩
theorem step8CommonScope32_valid : step8CommonScope32.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup32_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope32.sourceIndex step8CommonScope32_valid a))
    (step8CommonRawNeighbors (step8CommonScope32.neighborIndex step8CommonScope32_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope32.sourceIndex step8CommonScope32_valid a))
      (step8CommonNeighborAngles (step8CommonScope32.neighborIndex step8CommonScope32_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup32 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope32 step8CommonScope32_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup32_checked

def step8CommonScope33 : Scope := ⟨40, 8, 56, 4⟩
theorem step8CommonScope33_valid : step8CommonScope33.Valid 64 64 := by decide +kernel

def step8CommonPoint33 : CommonPoint.Point := ⟨9855, 10016, 10000⟩
kernel_matrix step8CommonGroup33_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope33.sourceIndex step8CommonScope33_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope33.sourceIndex step8CommonScope33_valid a))) step8CommonPoint33 = true)
kernel_matrix step8CommonGroup33_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope33.neighborIndex step8CommonScope33_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope33.neighborIndex step8CommonScope33_valid b))) step8CommonPoint33 = true)
def step8CommonGroup33 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope33 step8CommonScope33_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint33
  (fun a => step8CommonGroup33_sources a 0) (fun b => step8CommonGroup33_neighbors b 0)

def step8CommonScope34 : Scope := ⟨40, 8, 60, 4⟩
theorem step8CommonScope34_valid : step8CommonScope34.Valid 64 64 := by decide +kernel

def step8CommonPoint34 : CommonPoint.Point := ⟨99, 101, 100⟩
kernel_matrix step8CommonGroup34_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope34.sourceIndex step8CommonScope34_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope34.sourceIndex step8CommonScope34_valid a))) step8CommonPoint34 = true)
kernel_matrix step8CommonGroup34_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope34.neighborIndex step8CommonScope34_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope34.neighborIndex step8CommonScope34_valid b))) step8CommonPoint34 = true)
def step8CommonGroup34 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope34 step8CommonScope34_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint34
  (fun a => step8CommonGroup34_sources a 0) (fun b => step8CommonGroup34_neighbors b 0)

def step8CommonScope35 : Scope := ⟨48, 16, 48, 8⟩
theorem step8CommonScope35_valid : step8CommonScope35.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup35_checked : 16 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope35.sourceIndex step8CommonScope35_valid a))
    (step8CommonRawNeighbors (step8CommonScope35.neighborIndex step8CommonScope35_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope35.sourceIndex step8CommonScope35_valid a))
      (step8CommonNeighborAngles (step8CommonScope35.neighborIndex step8CommonScope35_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup35 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope35 step8CommonScope35_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup35_checked

def step8CommonScope36 : Scope := ⟨48, 8, 56, 8⟩
theorem step8CommonScope36_valid : step8CommonScope36.Valid 64 64 := by decide +kernel

def step8CommonPoint36 : CommonPoint.Point := ⟨989, 1032, 1000⟩
kernel_matrix step8CommonGroup36_sources : 8 × 1 => (fun a _ =>
  CommonPoint.check (step8CommonRawSources (step8CommonScope36.sourceIndex step8CommonScope36_valid a))
    (ownKeys (step8CommonSourceAngles (step8CommonScope36.sourceIndex step8CommonScope36_valid a))) step8CommonPoint36 = true)
kernel_matrix step8CommonGroup36_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step8CommonRawNeighbors (step8CommonScope36.neighborIndex step8CommonScope36_valid b))
    (ownKeys (step8CommonNeighborAngles (step8CommonScope36.neighborIndex step8CommonScope36_valid b))) step8CommonPoint36 = true)
def step8CommonGroup36 : CheckedGroup step8Sources step8Neighbors := pointGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope36 step8CommonScope36_valid
  (fun i => ownKeys (step8CommonSourceAngles i))
  (fun j => ownKeys (step8CommonNeighborAngles j)) step8CommonPoint36
  (fun a => step8CommonGroup36_sources a 0) (fun b => step8CommonGroup36_neighbors b 0)

def step8CommonScope37 : Scope := ⟨56, 8, 56, 8⟩
theorem step8CommonScope37_valid : step8CommonScope37.Valid 64 64 := by decide +kernel

kernel_matrix step8CommonGroup37_checked : 8 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step8CommonRawSources (step8CommonScope37.sourceIndex step8CommonScope37_valid a))
    (step8CommonRawNeighbors (step8CommonScope37.neighborIndex step8CommonScope37_valid b))
    (fanDirectionKey (step8CommonSourceAngles (step8CommonScope37.sourceIndex step8CommonScope37_valid a))
      (step8CommonNeighborAngles (step8CommonScope37.neighborIndex step8CommonScope37_valid b))) (fun key => (key + 128) % 256))
def step8CommonGroup37 : CheckedGroup step8Sources step8Neighbors := fallbackGroup
  step8Sources step8Neighbors
  step8CommonRawSources step8CommonRawNeighbors
  step8CommonRawSources_exact step8CommonRawNeighbors_exact
  step8CommonNeighborUnblocked step8CommonScope37 step8CommonScope37_valid
  step8CommonSourceAngles step8CommonNeighborAngles
  step8CommonSourceAngles_exact step8CommonNeighborAngles_exact
  step8CommonGroup37_checked

def step8CommonScopes : List Scope := [
  step8CommonScope0, step8CommonScope1, step8CommonScope2, step8CommonScope3, step8CommonScope4, step8CommonScope5, step8CommonScope6, step8CommonScope7, step8CommonScope8, step8CommonScope9, step8CommonScope10, step8CommonScope11, step8CommonScope12, step8CommonScope13, step8CommonScope14, step8CommonScope15, step8CommonScope16, step8CommonScope17, step8CommonScope18, step8CommonScope19, step8CommonScope20, step8CommonScope21, step8CommonScope22, step8CommonScope23, step8CommonScope24, step8CommonScope25, step8CommonScope26, step8CommonScope27, step8CommonScope28, step8CommonScope29, step8CommonScope30, step8CommonScope31, step8CommonScope32, step8CommonScope33, step8CommonScope34, step8CommonScope35, step8CommonScope36, step8CommonScope37]
def step8CommonGroups : List (CheckedGroup step8Sources step8Neighbors) := [
  step8CommonGroup0, step8CommonGroup1, step8CommonGroup2, step8CommonGroup3, step8CommonGroup4, step8CommonGroup5, step8CommonGroup6, step8CommonGroup7, step8CommonGroup8, step8CommonGroup9, step8CommonGroup10, step8CommonGroup11, step8CommonGroup12, step8CommonGroup13, step8CommonGroup14, step8CommonGroup15, step8CommonGroup16, step8CommonGroup17, step8CommonGroup18, step8CommonGroup19, step8CommonGroup20, step8CommonGroup21, step8CommonGroup22, step8CommonGroup23, step8CommonGroup24, step8CommonGroup25, step8CommonGroup26, step8CommonGroup27, step8CommonGroup28, step8CommonGroup29, step8CommonGroup30, step8CommonGroup31, step8CommonGroup32, step8CommonGroup33, step8CommonGroup34, step8CommonGroup35, step8CommonGroup36, step8CommonGroup37]
theorem step8CommonScopes_exact :
    step8CommonGroups.map CheckedGroup.scope = step8CommonScopes := rfl
kernel_matrix step8CommonCoverage : 64 × 64 => (fun i j =>
  ScopeCheck step8CommonScopes i.val j.val)
theorem step8_geometric_overlap (i : Fin 64) (j : Fin 64) :
    PairOverlaps (step8Sources i) (step8Neighbors j) :=
  groups_sound step8Sources step8Neighbors step8CommonGroups
    step8CommonScopes step8CommonScopes_exact step8CommonCoverage i j
#print axioms step8_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
