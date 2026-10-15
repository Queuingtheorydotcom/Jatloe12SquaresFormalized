import Compact.Cases.C898.CachedPairs.Step11CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step11CommonScope0 : Scope := ⟨0, 11, 0, 1⟩
theorem step11CommonScope0_valid : step11CommonScope0.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup0_checked : 11 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope0.sourceIndex step11CommonScope0_valid a))
    (step11CommonRawNeighbors (step11CommonScope0.neighborIndex step11CommonScope0_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope0.sourceIndex step11CommonScope0_valid a))
      (step11CommonNeighborAngles (step11CommonScope0.neighborIndex step11CommonScope0_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup0 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope0 step11CommonScope0_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup0_checked

def step11CommonScope1 : Scope := ⟨0, 11, 1, 2⟩
theorem step11CommonScope1_valid : step11CommonScope1.Valid 22 61 := by decide +kernel

def step11CommonPoint1 : CommonPoint.Point := ⟨1810, 1019, 1000⟩
kernel_matrix step11CommonGroup1_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope1.sourceIndex step11CommonScope1_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope1.sourceIndex step11CommonScope1_valid a))) step11CommonPoint1 = true)
kernel_matrix step11CommonGroup1_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope1.neighborIndex step11CommonScope1_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope1.neighborIndex step11CommonScope1_valid b))) step11CommonPoint1 = true)
def step11CommonGroup1 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope1 step11CommonScope1_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint1
  (fun a => step11CommonGroup1_sources a 0) (fun b => step11CommonGroup1_neighbors b 0)

def step11CommonScope2 : Scope := ⟨0, 11, 3, 4⟩
theorem step11CommonScope2_valid : step11CommonScope2.Valid 22 61 := by decide +kernel

def step11CommonPoint2 : CommonPoint.Point := ⟨1789, 1041, 1000⟩
kernel_matrix step11CommonGroup2_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope2.sourceIndex step11CommonScope2_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope2.sourceIndex step11CommonScope2_valid a))) step11CommonPoint2 = true)
kernel_matrix step11CommonGroup2_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope2.neighborIndex step11CommonScope2_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope2.neighborIndex step11CommonScope2_valid b))) step11CommonPoint2 = true)
def step11CommonGroup2 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope2 step11CommonScope2_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint2
  (fun a => step11CommonGroup2_sources a 0) (fun b => step11CommonGroup2_neighbors b 0)

def step11CommonScope3 : Scope := ⟨0, 5, 7, 8⟩
theorem step11CommonScope3_valid : step11CommonScope3.Valid 22 61 := by decide +kernel

def step11CommonPoint3 : CommonPoint.Point := ⟨1761, 1041, 1000⟩
kernel_matrix step11CommonGroup3_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope3.sourceIndex step11CommonScope3_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope3.sourceIndex step11CommonScope3_valid a))) step11CommonPoint3 = true)
kernel_matrix step11CommonGroup3_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope3.neighborIndex step11CommonScope3_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope3.neighborIndex step11CommonScope3_valid b))) step11CommonPoint3 = true)
def step11CommonGroup3 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope3 step11CommonScope3_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint3
  (fun a => step11CommonGroup3_sources a 0) (fun b => step11CommonGroup3_neighbors b 0)

def step11CommonScope4 : Scope := ⟨5, 6, 7, 8⟩
theorem step11CommonScope4_valid : step11CommonScope4.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup4_checked : 6 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope4.sourceIndex step11CommonScope4_valid a))
    (step11CommonRawNeighbors (step11CommonScope4.neighborIndex step11CommonScope4_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope4.sourceIndex step11CommonScope4_valid a))
      (step11CommonNeighborAngles (step11CommonScope4.neighborIndex step11CommonScope4_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup4 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope4 step11CommonScope4_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup4_checked

def step11CommonScope5 : Scope := ⟨11, 11, 0, 7⟩
theorem step11CommonScope5_valid : step11CommonScope5.Valid 22 61 := by decide +kernel

def step11CommonPoint5 : CommonPoint.Point := ⟨901, 495, 500⟩
kernel_matrix step11CommonGroup5_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope5.sourceIndex step11CommonScope5_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope5.sourceIndex step11CommonScope5_valid a))) step11CommonPoint5 = true)
kernel_matrix step11CommonGroup5_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope5.neighborIndex step11CommonScope5_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope5.neighborIndex step11CommonScope5_valid b))) step11CommonPoint5 = true)
def step11CommonGroup5 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope5 step11CommonScope5_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint5
  (fun a => step11CommonGroup5_sources a 0) (fun b => step11CommonGroup5_neighbors b 0)

def step11CommonScope6 : Scope := ⟨11, 2, 7, 8⟩
theorem step11CommonScope6_valid : step11CommonScope6.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup6_checked : 2 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope6.sourceIndex step11CommonScope6_valid a))
    (step11CommonRawNeighbors (step11CommonScope6.neighborIndex step11CommonScope6_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope6.sourceIndex step11CommonScope6_valid a))
      (step11CommonNeighborAngles (step11CommonScope6.neighborIndex step11CommonScope6_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup6 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope6 step11CommonScope6_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup6_checked

def step11CommonScope7 : Scope := ⟨13, 3, 7, 8⟩
theorem step11CommonScope7_valid : step11CommonScope7.Valid 22 61 := by decide +kernel

def step11CommonPoint7 : CommonPoint.Point := ⟨874, 541, 500⟩
kernel_matrix step11CommonGroup7_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope7.sourceIndex step11CommonScope7_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope7.sourceIndex step11CommonScope7_valid a))) step11CommonPoint7 = true)
kernel_matrix step11CommonGroup7_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope7.neighborIndex step11CommonScope7_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope7.neighborIndex step11CommonScope7_valid b))) step11CommonPoint7 = true)
def step11CommonGroup7 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope7 step11CommonScope7_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint7
  (fun a => step11CommonGroup7_sources a 0) (fun b => step11CommonGroup7_neighbors b 0)

def step11CommonScope8 : Scope := ⟨16, 6, 7, 8⟩
theorem step11CommonScope8_valid : step11CommonScope8.Valid 22 61 := by decide +kernel

def step11CommonPoint8 : CommonPoint.Point := ⟨1745, 1079, 1000⟩
kernel_matrix step11CommonGroup8_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope8.sourceIndex step11CommonScope8_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope8.sourceIndex step11CommonScope8_valid a))) step11CommonPoint8 = true)
kernel_matrix step11CommonGroup8_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope8.neighborIndex step11CommonScope8_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope8.neighborIndex step11CommonScope8_valid b))) step11CommonPoint8 = true)
def step11CommonGroup8 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope8 step11CommonScope8_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint8
  (fun a => step11CommonGroup8_sources a 0) (fun b => step11CommonGroup8_neighbors b 0)

def step11CommonScope9 : Scope := ⟨0, 5, 15, 15⟩
theorem step11CommonScope9_valid : step11CommonScope9.Valid 22 61 := by decide +kernel

def step11CommonPoint9 : CommonPoint.Point := ⟨883, 510, 500⟩
kernel_matrix step11CommonGroup9_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope9.sourceIndex step11CommonScope9_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope9.sourceIndex step11CommonScope9_valid a))) step11CommonPoint9 = true)
kernel_matrix step11CommonGroup9_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope9.neighborIndex step11CommonScope9_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope9.neighborIndex step11CommonScope9_valid b))) step11CommonPoint9 = true)
def step11CommonGroup9 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope9 step11CommonScope9_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint9
  (fun a => step11CommonGroup9_sources a 0) (fun b => step11CommonGroup9_neighbors b 0)

def step11CommonScope10 : Scope := ⟨5, 1, 15, 15⟩
theorem step11CommonScope10_valid : step11CommonScope10.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup10_checked : 1 × 15 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope10.sourceIndex step11CommonScope10_valid a))
    (step11CommonRawNeighbors (step11CommonScope10.neighborIndex step11CommonScope10_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope10.sourceIndex step11CommonScope10_valid a))
      (step11CommonNeighborAngles (step11CommonScope10.neighborIndex step11CommonScope10_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup10 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope10 step11CommonScope10_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup10_checked

def step11CommonScope11 : Scope := ⟨6, 2, 15, 15⟩
theorem step11CommonScope11_valid : step11CommonScope11.Valid 22 61 := by decide +kernel

def step11CommonPoint11 : CommonPoint.Point := ⟨1789, 997, 1000⟩
kernel_matrix step11CommonGroup11_sources : 2 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope11.sourceIndex step11CommonScope11_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope11.sourceIndex step11CommonScope11_valid a))) step11CommonPoint11 = true)
kernel_matrix step11CommonGroup11_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope11.neighborIndex step11CommonScope11_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope11.neighborIndex step11CommonScope11_valid b))) step11CommonPoint11 = true)
def step11CommonGroup11 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope11 step11CommonScope11_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint11
  (fun a => step11CommonGroup11_sources a 0) (fun b => step11CommonGroup11_neighbors b 0)

def step11CommonScope12 : Scope := ⟨8, 3, 15, 15⟩
theorem step11CommonScope12_valid : step11CommonScope12.Valid 22 61 := by decide +kernel

def step11CommonPoint12 : CommonPoint.Point := ⟨1793, 990, 1000⟩
kernel_matrix step11CommonGroup12_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope12.sourceIndex step11CommonScope12_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope12.sourceIndex step11CommonScope12_valid a))) step11CommonPoint12 = true)
kernel_matrix step11CommonGroup12_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope12.neighborIndex step11CommonScope12_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope12.neighborIndex step11CommonScope12_valid b))) step11CommonPoint12 = true)
def step11CommonGroup12 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope12 step11CommonScope12_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint12
  (fun a => step11CommonGroup12_sources a 0) (fun b => step11CommonGroup12_neighbors b 0)

def step11CommonScope13 : Scope := ⟨11, 5, 15, 3⟩
theorem step11CommonScope13_valid : step11CommonScope13.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup13_checked : 5 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope13.sourceIndex step11CommonScope13_valid a))
    (step11CommonRawNeighbors (step11CommonScope13.neighborIndex step11CommonScope13_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope13.sourceIndex step11CommonScope13_valid a))
      (step11CommonNeighborAngles (step11CommonScope13.neighborIndex step11CommonScope13_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup13 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope13 step11CommonScope13_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup13_checked

def step11CommonScope14 : Scope := ⟨11, 5, 18, 4⟩
theorem step11CommonScope14_valid : step11CommonScope14.Valid 22 61 := by decide +kernel

def step11CommonPoint14 : CommonPoint.Point := ⟨18005, 9791, 10000⟩
kernel_matrix step11CommonGroup14_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope14.sourceIndex step11CommonScope14_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope14.sourceIndex step11CommonScope14_valid a))) step11CommonPoint14 = true)
kernel_matrix step11CommonGroup14_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope14.neighborIndex step11CommonScope14_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope14.neighborIndex step11CommonScope14_valid b))) step11CommonPoint14 = true)
def step11CommonGroup14 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope14 step11CommonScope14_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint14
  (fun a => step11CommonGroup14_sources a 0) (fun b => step11CommonGroup14_neighbors b 0)

def step11CommonScope15 : Scope := ⟨16, 3, 15, 7⟩
theorem step11CommonScope15_valid : step11CommonScope15.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup15_checked : 3 × 7 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope15.sourceIndex step11CommonScope15_valid a))
    (step11CommonRawNeighbors (step11CommonScope15.neighborIndex step11CommonScope15_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope15.sourceIndex step11CommonScope15_valid a))
      (step11CommonNeighborAngles (step11CommonScope15.neighborIndex step11CommonScope15_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup15 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope15 step11CommonScope15_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup15_checked

def step11CommonScope16 : Scope := ⟨19, 3, 15, 7⟩
theorem step11CommonScope16_valid : step11CommonScope16.Valid 22 61 := by decide +kernel

def step11CommonPoint16 : CommonPoint.Point := ⟨1691127, 1128180, 1000000⟩
kernel_matrix step11CommonGroup16_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope16.sourceIndex step11CommonScope16_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope16.sourceIndex step11CommonScope16_valid a))) step11CommonPoint16 = true)
kernel_matrix step11CommonGroup16_neighbors : 7 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope16.neighborIndex step11CommonScope16_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope16.neighborIndex step11CommonScope16_valid b))) step11CommonPoint16 = true)
def step11CommonGroup16 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope16 step11CommonScope16_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint16
  (fun a => step11CommonGroup16_sources a 0) (fun b => step11CommonGroup16_neighbors b 0)

def step11CommonScope17 : Scope := ⟨11, 5, 22, 4⟩
theorem step11CommonScope17_valid : step11CommonScope17.Valid 22 61 := by decide +kernel

def step11CommonPoint17 : CommonPoint.Point := ⟨1799, 984, 1000⟩
kernel_matrix step11CommonGroup17_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope17.sourceIndex step11CommonScope17_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope17.sourceIndex step11CommonScope17_valid a))) step11CommonPoint17 = true)
kernel_matrix step11CommonGroup17_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope17.neighborIndex step11CommonScope17_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope17.neighborIndex step11CommonScope17_valid b))) step11CommonPoint17 = true)
def step11CommonGroup17 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope17 step11CommonScope17_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint17
  (fun a => step11CommonGroup17_sources a 0) (fun b => step11CommonGroup17_neighbors b 0)

def step11CommonScope18 : Scope := ⟨16, 3, 22, 4⟩
theorem step11CommonScope18_valid : step11CommonScope18.Valid 22 61 := by decide +kernel

def step11CommonPoint18 : CommonPoint.Point := ⟨1821, 956, 1000⟩
kernel_matrix step11CommonGroup18_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope18.sourceIndex step11CommonScope18_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope18.sourceIndex step11CommonScope18_valid a))) step11CommonPoint18 = true)
kernel_matrix step11CommonGroup18_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope18.neighborIndex step11CommonScope18_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope18.neighborIndex step11CommonScope18_valid b))) step11CommonPoint18 = true)
def step11CommonGroup18 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope18 step11CommonScope18_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint18
  (fun a => step11CommonGroup18_sources a 0) (fun b => step11CommonGroup18_neighbors b 0)

def step11CommonScope19 : Scope := ⟨19, 3, 22, 4⟩
theorem step11CommonScope19_valid : step11CommonScope19.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup19_checked : 3 × 4 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope19.sourceIndex step11CommonScope19_valid a))
    (step11CommonRawNeighbors (step11CommonScope19.neighborIndex step11CommonScope19_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope19.sourceIndex step11CommonScope19_valid a))
      (step11CommonNeighborAngles (step11CommonScope19.neighborIndex step11CommonScope19_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup19 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope19 step11CommonScope19_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup19_checked

def step11CommonScope20 : Scope := ⟨11, 11, 26, 4⟩
theorem step11CommonScope20_valid : step11CommonScope20.Valid 22 61 := by decide +kernel

def step11CommonPoint20 : CommonPoint.Point := ⟨1807, 983, 1000⟩
kernel_matrix step11CommonGroup20_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope20.sourceIndex step11CommonScope20_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope20.sourceIndex step11CommonScope20_valid a))) step11CommonPoint20 = true)
kernel_matrix step11CommonGroup20_neighbors : 4 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope20.neighborIndex step11CommonScope20_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope20.neighborIndex step11CommonScope20_valid b))) step11CommonPoint20 = true)
def step11CommonGroup20 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope20 step11CommonScope20_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint20
  (fun a => step11CommonGroup20_sources a 0) (fun b => step11CommonGroup20_neighbors b 0)

def step11CommonScope21 : Scope := ⟨0, 5, 30, 15⟩
theorem step11CommonScope21_valid : step11CommonScope21.Valid 22 61 := by decide +kernel

def step11CommonPoint21 : CommonPoint.Point := ⟨885, 508, 500⟩
kernel_matrix step11CommonGroup21_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope21.sourceIndex step11CommonScope21_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope21.sourceIndex step11CommonScope21_valid a))) step11CommonPoint21 = true)
kernel_matrix step11CommonGroup21_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope21.neighborIndex step11CommonScope21_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope21.neighborIndex step11CommonScope21_valid b))) step11CommonPoint21 = true)
def step11CommonGroup21 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope21 step11CommonScope21_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint21
  (fun a => step11CommonGroup21_sources a 0) (fun b => step11CommonGroup21_neighbors b 0)

def step11CommonScope22 : Scope := ⟨5, 6, 30, 15⟩
theorem step11CommonScope22_valid : step11CommonScope22.Valid 22 61 := by decide +kernel

def step11CommonPoint22 : CommonPoint.Point := ⟨358, 201, 200⟩
kernel_matrix step11CommonGroup22_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope22.sourceIndex step11CommonScope22_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope22.sourceIndex step11CommonScope22_valid a))) step11CommonPoint22 = true)
kernel_matrix step11CommonGroup22_neighbors : 15 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope22.neighborIndex step11CommonScope22_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope22.neighborIndex step11CommonScope22_valid b))) step11CommonPoint22 = true)
def step11CommonGroup22 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope22 step11CommonScope22_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint22
  (fun a => step11CommonGroup22_sources a 0) (fun b => step11CommonGroup22_neighbors b 0)

def step11CommonScope23 : Scope := ⟨0, 5, 45, 8⟩
theorem step11CommonScope23_valid : step11CommonScope23.Valid 22 61 := by decide +kernel

def step11CommonPoint23 : CommonPoint.Point := ⟨1761, 1013, 1000⟩
kernel_matrix step11CommonGroup23_sources : 5 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope23.sourceIndex step11CommonScope23_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope23.sourceIndex step11CommonScope23_valid a))) step11CommonPoint23 = true)
kernel_matrix step11CommonGroup23_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope23.neighborIndex step11CommonScope23_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope23.neighborIndex step11CommonScope23_valid b))) step11CommonPoint23 = true)
def step11CommonGroup23 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope23 step11CommonScope23_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint23
  (fun a => step11CommonGroup23_sources a 0) (fun b => step11CommonGroup23_neighbors b 0)

def step11CommonScope24 : Scope := ⟨5, 6, 45, 8⟩
theorem step11CommonScope24_valid : step11CommonScope24.Valid 22 61 := by decide +kernel

def step11CommonPoint24 : CommonPoint.Point := ⟨897, 504, 500⟩
kernel_matrix step11CommonGroup24_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope24.sourceIndex step11CommonScope24_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope24.sourceIndex step11CommonScope24_valid a))) step11CommonPoint24 = true)
kernel_matrix step11CommonGroup24_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope24.neighborIndex step11CommonScope24_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope24.neighborIndex step11CommonScope24_valid b))) step11CommonPoint24 = true)
def step11CommonGroup24 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope24 step11CommonScope24_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint24
  (fun a => step11CommonGroup24_sources a 0) (fun b => step11CommonGroup24_neighbors b 0)

def step11CommonScope25 : Scope := ⟨0, 5, 53, 8⟩
theorem step11CommonScope25_valid : step11CommonScope25.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup25_checked : 5 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope25.sourceIndex step11CommonScope25_valid a))
    (step11CommonRawNeighbors (step11CommonScope25.neighborIndex step11CommonScope25_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope25.sourceIndex step11CommonScope25_valid a))
      (step11CommonNeighborAngles (step11CommonScope25.neighborIndex step11CommonScope25_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup25 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope25 step11CommonScope25_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup25_checked

def step11CommonScope26 : Scope := ⟨5, 3, 53, 8⟩
theorem step11CommonScope26_valid : step11CommonScope26.Valid 22 61 := by decide +kernel

kernel_matrix step11CommonGroup26_checked : 3 × 8 => (fun a b =>
  RawSupportFan.PairCheck (step11CommonRawSources (step11CommonScope26.sourceIndex step11CommonScope26_valid a))
    (step11CommonRawNeighbors (step11CommonScope26.neighborIndex step11CommonScope26_valid b))
    (fanDirectionKey (step11CommonSourceAngles (step11CommonScope26.sourceIndex step11CommonScope26_valid a))
      (step11CommonNeighborAngles (step11CommonScope26.neighborIndex step11CommonScope26_valid b))) (fun key => (key + 128) % 256))
def step11CommonGroup26 : CheckedGroup step11Sources step11Neighbors := fallbackGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope26 step11CommonScope26_valid
  step11CommonSourceAngles step11CommonNeighborAngles
  step11CommonSourceAngles_exact step11CommonNeighborAngles_exact
  step11CommonGroup26_checked

def step11CommonScope27 : Scope := ⟨8, 3, 53, 8⟩
theorem step11CommonScope27_valid : step11CommonScope27.Valid 22 61 := by decide +kernel

def step11CommonPoint27 : CommonPoint.Point := ⟨452, 247, 250⟩
kernel_matrix step11CommonGroup27_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope27.sourceIndex step11CommonScope27_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope27.sourceIndex step11CommonScope27_valid a))) step11CommonPoint27 = true)
kernel_matrix step11CommonGroup27_neighbors : 8 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope27.neighborIndex step11CommonScope27_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope27.neighborIndex step11CommonScope27_valid b))) step11CommonPoint27 = true)
def step11CommonGroup27 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope27 step11CommonScope27_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint27
  (fun a => step11CommonGroup27_sources a 0) (fun b => step11CommonGroup27_neighbors b 0)

def step11CommonScope28 : Scope := ⟨11, 11, 30, 31⟩
theorem step11CommonScope28_valid : step11CommonScope28.Valid 22 61 := by decide +kernel

def step11CommonPoint28 : CommonPoint.Point := ⟨908, 489, 500⟩
kernel_matrix step11CommonGroup28_sources : 11 × 1 => (fun a _ =>
  CommonPoint.check (step11CommonRawSources (step11CommonScope28.sourceIndex step11CommonScope28_valid a))
    (ownKeys (step11CommonSourceAngles (step11CommonScope28.sourceIndex step11CommonScope28_valid a))) step11CommonPoint28 = true)
kernel_matrix step11CommonGroup28_neighbors : 31 × 1 => (fun b _ =>
  CommonPoint.check (step11CommonRawNeighbors (step11CommonScope28.neighborIndex step11CommonScope28_valid b))
    (ownKeys (step11CommonNeighborAngles (step11CommonScope28.neighborIndex step11CommonScope28_valid b))) step11CommonPoint28 = true)
def step11CommonGroup28 : CheckedGroup step11Sources step11Neighbors := pointGroup
  step11Sources step11Neighbors
  step11CommonRawSources step11CommonRawNeighbors
  step11CommonRawSources_exact step11CommonRawNeighbors_exact
  step11CommonNeighborUnblocked step11CommonScope28 step11CommonScope28_valid
  (fun i => ownKeys (step11CommonSourceAngles i))
  (fun j => ownKeys (step11CommonNeighborAngles j)) step11CommonPoint28
  (fun a => step11CommonGroup28_sources a 0) (fun b => step11CommonGroup28_neighbors b 0)

def step11CommonScopes : List Scope := [
  step11CommonScope0, step11CommonScope1, step11CommonScope2, step11CommonScope3, step11CommonScope4, step11CommonScope5, step11CommonScope6, step11CommonScope7, step11CommonScope8, step11CommonScope9, step11CommonScope10, step11CommonScope11, step11CommonScope12, step11CommonScope13, step11CommonScope14, step11CommonScope15, step11CommonScope16, step11CommonScope17, step11CommonScope18, step11CommonScope19, step11CommonScope20, step11CommonScope21, step11CommonScope22, step11CommonScope23, step11CommonScope24, step11CommonScope25, step11CommonScope26, step11CommonScope27, step11CommonScope28]
def step11CommonGroups : List (CheckedGroup step11Sources step11Neighbors) := [
  step11CommonGroup0, step11CommonGroup1, step11CommonGroup2, step11CommonGroup3, step11CommonGroup4, step11CommonGroup5, step11CommonGroup6, step11CommonGroup7, step11CommonGroup8, step11CommonGroup9, step11CommonGroup10, step11CommonGroup11, step11CommonGroup12, step11CommonGroup13, step11CommonGroup14, step11CommonGroup15, step11CommonGroup16, step11CommonGroup17, step11CommonGroup18, step11CommonGroup19, step11CommonGroup20, step11CommonGroup21, step11CommonGroup22, step11CommonGroup23, step11CommonGroup24, step11CommonGroup25, step11CommonGroup26, step11CommonGroup27, step11CommonGroup28]
theorem step11CommonScopes_exact :
    step11CommonGroups.map CheckedGroup.scope = step11CommonScopes := rfl
kernel_matrix step11CommonCoverage : 22 × 61 => (fun i j =>
  ScopeCheck step11CommonScopes i.val j.val)
theorem step11_geometric_overlap (i : Fin 22) (j : Fin 61) :
    PairOverlaps (step11Sources i) (step11Neighbors j) :=
  groups_sound step11Sources step11Neighbors step11CommonGroups
    step11CommonScopes step11CommonScopes_exact step11CommonCoverage i j
#print axioms step11_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
