import Compact.Cases.C898.CachedPairs.Step05CommonData

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step5CommonScope0 : Scope := ⟨0, 6, 0, 3⟩
theorem step5CommonScope0_valid : step5CommonScope0.Valid 51 12 := by decide +kernel

def step5CommonPoint0 : CommonPoint.Point := ⟨297, 279, 125⟩
kernel_matrix step5CommonGroup0_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope0.sourceIndex step5CommonScope0_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope0.sourceIndex step5CommonScope0_valid a))) step5CommonPoint0 = true)
kernel_matrix step5CommonGroup0_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope0.neighborIndex step5CommonScope0_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope0.neighborIndex step5CommonScope0_valid b))) step5CommonPoint0 = true)
def step5CommonGroup0 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope0 step5CommonScope0_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint0
  (fun a => step5CommonGroup0_sources a 0) (fun b => step5CommonGroup0_neighbors b 0)

def step5CommonScope1 : Scope := ⟨0, 6, 3, 3⟩
theorem step5CommonScope1_valid : step5CommonScope1.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup1_checked : 6 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope1.sourceIndex step5CommonScope1_valid a))
    (step5CommonRawNeighbors (step5CommonScope1.neighborIndex step5CommonScope1_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope1.sourceIndex step5CommonScope1_valid a))
      (step5CommonNeighborAngles (step5CommonScope1.neighborIndex step5CommonScope1_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup1 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope1 step5CommonScope1_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup1_checked

def step5CommonScope2 : Scope := ⟨6, 3, 0, 3⟩
theorem step5CommonScope2_valid : step5CommonScope2.Valid 51 12 := by decide +kernel

def step5CommonPoint2 : CommonPoint.Point := ⟨23745, 22417, 10000⟩
kernel_matrix step5CommonGroup2_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope2.sourceIndex step5CommonScope2_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope2.sourceIndex step5CommonScope2_valid a))) step5CommonPoint2 = true)
kernel_matrix step5CommonGroup2_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope2.neighborIndex step5CommonScope2_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope2.neighborIndex step5CommonScope2_valid b))) step5CommonPoint2 = true)
def step5CommonGroup2 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope2 step5CommonScope2_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint2
  (fun a => step5CommonGroup2_sources a 0) (fun b => step5CommonGroup2_neighbors b 0)

def step5CommonScope3 : Scope := ⟨9, 1, 0, 3⟩
theorem step5CommonScope3_valid : step5CommonScope3.Valid 51 12 := by decide +kernel

def step5CommonPoint3 : CommonPoint.Point := ⟨1189, 1128, 500⟩
kernel_matrix step5CommonGroup3_sources : 1 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope3.sourceIndex step5CommonScope3_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope3.sourceIndex step5CommonScope3_valid a))) step5CommonPoint3 = true)
kernel_matrix step5CommonGroup3_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope3.neighborIndex step5CommonScope3_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope3.neighborIndex step5CommonScope3_valid b))) step5CommonPoint3 = true)
def step5CommonGroup3 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope3 step5CommonScope3_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint3
  (fun a => step5CommonGroup3_sources a 0) (fun b => step5CommonGroup3_neighbors b 0)

def step5CommonScope4 : Scope := ⟨10, 2, 0, 3⟩
theorem step5CommonScope4_valid : step5CommonScope4.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup4_checked : 2 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope4.sourceIndex step5CommonScope4_valid a))
    (step5CommonRawNeighbors (step5CommonScope4.neighborIndex step5CommonScope4_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope4.sourceIndex step5CommonScope4_valid a))
      (step5CommonNeighborAngles (step5CommonScope4.neighborIndex step5CommonScope4_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup4 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope4 step5CommonScope4_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup4_checked

def step5CommonScope5 : Scope := ⟨6, 3, 3, 3⟩
theorem step5CommonScope5_valid : step5CommonScope5.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup5_checked : 3 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope5.sourceIndex step5CommonScope5_valid a))
    (step5CommonRawNeighbors (step5CommonScope5.neighborIndex step5CommonScope5_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope5.sourceIndex step5CommonScope5_valid a))
      (step5CommonNeighborAngles (step5CommonScope5.neighborIndex step5CommonScope5_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup5 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope5 step5CommonScope5_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup5_checked

def step5CommonScope6 : Scope := ⟨9, 1, 3, 3⟩
theorem step5CommonScope6_valid : step5CommonScope6.Valid 51 12 := by decide +kernel

def step5CommonPoint6 : CommonPoint.Point := ⟨1192, 1127, 500⟩
kernel_matrix step5CommonGroup6_sources : 1 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope6.sourceIndex step5CommonScope6_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope6.sourceIndex step5CommonScope6_valid a))) step5CommonPoint6 = true)
kernel_matrix step5CommonGroup6_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope6.neighborIndex step5CommonScope6_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope6.neighborIndex step5CommonScope6_valid b))) step5CommonPoint6 = true)
def step5CommonGroup6 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope6 step5CommonScope6_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint6
  (fun a => step5CommonGroup6_sources a 0) (fun b => step5CommonGroup6_neighbors b 0)

def step5CommonScope7 : Scope := ⟨10, 2, 3, 3⟩
theorem step5CommonScope7_valid : step5CommonScope7.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup7_checked : 2 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope7.sourceIndex step5CommonScope7_valid a))
    (step5CommonRawNeighbors (step5CommonScope7.neighborIndex step5CommonScope7_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope7.sourceIndex step5CommonScope7_valid a))
      (step5CommonNeighborAngles (step5CommonScope7.neighborIndex step5CommonScope7_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup7 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope7 step5CommonScope7_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup7_checked

def step5CommonScope8 : Scope := ⟨0, 12, 6, 6⟩
theorem step5CommonScope8_valid : step5CommonScope8.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup8_checked : 12 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope8.sourceIndex step5CommonScope8_valid a))
    (step5CommonRawNeighbors (step5CommonScope8.neighborIndex step5CommonScope8_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope8.sourceIndex step5CommonScope8_valid a))
      (step5CommonNeighborAngles (step5CommonScope8.neighborIndex step5CommonScope8_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup8 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope8 step5CommonScope8_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup8_checked

def step5CommonScope9 : Scope := ⟨12, 6, 0, 12⟩
theorem step5CommonScope9_valid : step5CommonScope9.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup9_checked : 6 × 12 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope9.sourceIndex step5CommonScope9_valid a))
    (step5CommonRawNeighbors (step5CommonScope9.neighborIndex step5CommonScope9_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope9.sourceIndex step5CommonScope9_valid a))
      (step5CommonNeighborAngles (step5CommonScope9.neighborIndex step5CommonScope9_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup9 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope9 step5CommonScope9_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup9_checked

def step5CommonScope10 : Scope := ⟨18, 7, 0, 6⟩
theorem step5CommonScope10_valid : step5CommonScope10.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup10_checked : 7 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope10.sourceIndex step5CommonScope10_valid a))
    (step5CommonRawNeighbors (step5CommonScope10.neighborIndex step5CommonScope10_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope10.sourceIndex step5CommonScope10_valid a))
      (step5CommonNeighborAngles (step5CommonScope10.neighborIndex step5CommonScope10_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup10 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope10 step5CommonScope10_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup10_checked

def step5CommonScope11 : Scope := ⟨18, 1, 6, 6⟩
theorem step5CommonScope11_valid : step5CommonScope11.Valid 51 12 := by decide +kernel

def step5CommonPoint11 : CommonPoint.Point := ⟨1181, 1186, 500⟩
kernel_matrix step5CommonGroup11_sources : 1 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope11.sourceIndex step5CommonScope11_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope11.sourceIndex step5CommonScope11_valid a))) step5CommonPoint11 = true)
kernel_matrix step5CommonGroup11_neighbors : 6 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope11.neighborIndex step5CommonScope11_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope11.neighborIndex step5CommonScope11_valid b))) step5CommonPoint11 = true)
def step5CommonGroup11 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope11 step5CommonScope11_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint11
  (fun a => step5CommonGroup11_sources a 0) (fun b => step5CommonGroup11_neighbors b 0)

def step5CommonScope12 : Scope := ⟨19, 2, 6, 6⟩
theorem step5CommonScope12_valid : step5CommonScope12.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup12_checked : 2 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope12.sourceIndex step5CommonScope12_valid a))
    (step5CommonRawNeighbors (step5CommonScope12.neighborIndex step5CommonScope12_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope12.sourceIndex step5CommonScope12_valid a))
      (step5CommonNeighborAngles (step5CommonScope12.neighborIndex step5CommonScope12_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup12 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope12 step5CommonScope12_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup12_checked

def step5CommonScope13 : Scope := ⟨21, 4, 6, 6⟩
theorem step5CommonScope13_valid : step5CommonScope13.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup13_checked : 4 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope13.sourceIndex step5CommonScope13_valid a))
    (step5CommonRawNeighbors (step5CommonScope13.neighborIndex step5CommonScope13_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope13.sourceIndex step5CommonScope13_valid a))
      (step5CommonNeighborAngles (step5CommonScope13.neighborIndex step5CommonScope13_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup13 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope13 step5CommonScope13_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup13_checked

def step5CommonScope14 : Scope := ⟨25, 6, 0, 12⟩
theorem step5CommonScope14_valid : step5CommonScope14.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup14_checked : 6 × 12 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope14.sourceIndex step5CommonScope14_valid a))
    (step5CommonRawNeighbors (step5CommonScope14.neighborIndex step5CommonScope14_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope14.sourceIndex step5CommonScope14_valid a))
      (step5CommonNeighborAngles (step5CommonScope14.neighborIndex step5CommonScope14_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup14 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope14 step5CommonScope14_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup14_checked

def step5CommonScope15 : Scope := ⟨31, 7, 0, 6⟩
theorem step5CommonScope15_valid : step5CommonScope15.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup15_checked : 7 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope15.sourceIndex step5CommonScope15_valid a))
    (step5CommonRawNeighbors (step5CommonScope15.neighborIndex step5CommonScope15_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope15.sourceIndex step5CommonScope15_valid a))
      (step5CommonNeighborAngles (step5CommonScope15.neighborIndex step5CommonScope15_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup15 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope15 step5CommonScope15_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup15_checked

def step5CommonScope16 : Scope := ⟨31, 3, 6, 6⟩
theorem step5CommonScope16_valid : step5CommonScope16.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup16_checked : 3 × 6 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope16.sourceIndex step5CommonScope16_valid a))
    (step5CommonRawNeighbors (step5CommonScope16.neighborIndex step5CommonScope16_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope16.sourceIndex step5CommonScope16_valid a))
      (step5CommonNeighborAngles (step5CommonScope16.neighborIndex step5CommonScope16_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup16 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope16 step5CommonScope16_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup16_checked

def step5CommonScope17 : Scope := ⟨34, 4, 6, 1⟩
theorem step5CommonScope17_valid : step5CommonScope17.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup17_checked : 4 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope17.sourceIndex step5CommonScope17_valid a))
    (step5CommonRawNeighbors (step5CommonScope17.neighborIndex step5CommonScope17_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope17.sourceIndex step5CommonScope17_valid a))
      (step5CommonNeighborAngles (step5CommonScope17.neighborIndex step5CommonScope17_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup17 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope17 step5CommonScope17_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup17_checked

def step5CommonScope18 : Scope := ⟨34, 4, 7, 2⟩
theorem step5CommonScope18_valid : step5CommonScope18.Valid 51 12 := by decide +kernel

def step5CommonPoint18 : CommonPoint.Point := ⟨577, 649, 250⟩
kernel_matrix step5CommonGroup18_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope18.sourceIndex step5CommonScope18_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope18.sourceIndex step5CommonScope18_valid a))) step5CommonPoint18 = true)
kernel_matrix step5CommonGroup18_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope18.neighborIndex step5CommonScope18_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope18.neighborIndex step5CommonScope18_valid b))) step5CommonPoint18 = true)
def step5CommonGroup18 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope18 step5CommonScope18_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint18
  (fun a => step5CommonGroup18_sources a 0) (fun b => step5CommonGroup18_neighbors b 0)

def step5CommonScope19 : Scope := ⟨34, 4, 9, 1⟩
theorem step5CommonScope19_valid : step5CommonScope19.Valid 51 12 := by decide +kernel

def step5CommonPoint19 : CommonPoint.Point := ⟨2302, 2591, 1000⟩
kernel_matrix step5CommonGroup19_sources : 4 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope19.sourceIndex step5CommonScope19_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope19.sourceIndex step5CommonScope19_valid a))) step5CommonPoint19 = true)
kernel_matrix step5CommonGroup19_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope19.neighborIndex step5CommonScope19_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope19.neighborIndex step5CommonScope19_valid b))) step5CommonPoint19 = true)
def step5CommonGroup19 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope19 step5CommonScope19_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint19
  (fun a => step5CommonGroup19_sources a 0) (fun b => step5CommonGroup19_neighbors b 0)

def step5CommonScope20 : Scope := ⟨34, 4, 10, 2⟩
theorem step5CommonScope20_valid : step5CommonScope20.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup20_checked : 4 × 2 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope20.sourceIndex step5CommonScope20_valid a))
    (step5CommonRawNeighbors (step5CommonScope20.neighborIndex step5CommonScope20_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope20.sourceIndex step5CommonScope20_valid a))
      (step5CommonNeighborAngles (step5CommonScope20.neighborIndex step5CommonScope20_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup20 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope20 step5CommonScope20_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup20_checked

def step5CommonScope21 : Scope := ⟨38, 6, 0, 3⟩
theorem step5CommonScope21_valid : step5CommonScope21.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup21_checked : 6 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope21.sourceIndex step5CommonScope21_valid a))
    (step5CommonRawNeighbors (step5CommonScope21.neighborIndex step5CommonScope21_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope21.sourceIndex step5CommonScope21_valid a))
      (step5CommonNeighborAngles (step5CommonScope21.neighborIndex step5CommonScope21_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup21 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope21 step5CommonScope21_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup21_checked

def step5CommonScope22 : Scope := ⟨38, 3, 3, 3⟩
theorem step5CommonScope22_valid : step5CommonScope22.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup22_checked : 3 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope22.sourceIndex step5CommonScope22_valid a))
    (step5CommonRawNeighbors (step5CommonScope22.neighborIndex step5CommonScope22_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope22.sourceIndex step5CommonScope22_valid a))
      (step5CommonNeighborAngles (step5CommonScope22.neighborIndex step5CommonScope22_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup22 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope22 step5CommonScope22_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup22_checked

def step5CommonScope23 : Scope := ⟨41, 3, 3, 1⟩
theorem step5CommonScope23_valid : step5CommonScope23.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup23_checked : 3 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope23.sourceIndex step5CommonScope23_valid a))
    (step5CommonRawNeighbors (step5CommonScope23.neighborIndex step5CommonScope23_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope23.sourceIndex step5CommonScope23_valid a))
      (step5CommonNeighborAngles (step5CommonScope23.neighborIndex step5CommonScope23_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup23 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope23 step5CommonScope23_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup23_checked

def step5CommonScope24 : Scope := ⟨41, 3, 4, 2⟩
theorem step5CommonScope24_valid : step5CommonScope24.Valid 51 12 := by decide +kernel

def step5CommonPoint24 : CommonPoint.Point := ⟨2324, 2657, 1000⟩
kernel_matrix step5CommonGroup24_sources : 3 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope24.sourceIndex step5CommonScope24_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope24.sourceIndex step5CommonScope24_valid a))) step5CommonPoint24 = true)
kernel_matrix step5CommonGroup24_neighbors : 2 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope24.neighborIndex step5CommonScope24_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope24.neighborIndex step5CommonScope24_valid b))) step5CommonPoint24 = true)
def step5CommonGroup24 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope24 step5CommonScope24_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint24
  (fun a => step5CommonGroup24_sources a 0) (fun b => step5CommonGroup24_neighbors b 0)

def step5CommonScope25 : Scope := ⟨38, 6, 6, 3⟩
theorem step5CommonScope25_valid : step5CommonScope25.Valid 51 12 := by decide +kernel

def step5CommonPoint25 : CommonPoint.Point := ⟨2313, 2629, 1000⟩
kernel_matrix step5CommonGroup25_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope25.sourceIndex step5CommonScope25_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope25.sourceIndex step5CommonScope25_valid a))) step5CommonPoint25 = true)
kernel_matrix step5CommonGroup25_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope25.neighborIndex step5CommonScope25_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope25.neighborIndex step5CommonScope25_valid b))) step5CommonPoint25 = true)
def step5CommonGroup25 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope25 step5CommonScope25_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint25
  (fun a => step5CommonGroup25_sources a 0) (fun b => step5CommonGroup25_neighbors b 0)

def step5CommonScope26 : Scope := ⟨38, 6, 9, 1⟩
theorem step5CommonScope26_valid : step5CommonScope26.Valid 51 12 := by decide +kernel

def step5CommonPoint26 : CommonPoint.Point := ⟨2299, 2615, 1000⟩
kernel_matrix step5CommonGroup26_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope26.sourceIndex step5CommonScope26_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope26.sourceIndex step5CommonScope26_valid a))) step5CommonPoint26 = true)
kernel_matrix step5CommonGroup26_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope26.neighborIndex step5CommonScope26_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope26.neighborIndex step5CommonScope26_valid b))) step5CommonPoint26 = true)
def step5CommonGroup26 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope26 step5CommonScope26_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint26
  (fun a => step5CommonGroup26_sources a 0) (fun b => step5CommonGroup26_neighbors b 0)

def step5CommonScope27 : Scope := ⟨38, 6, 10, 1⟩
theorem step5CommonScope27_valid : step5CommonScope27.Valid 51 12 := by decide +kernel

def step5CommonPoint27 : CommonPoint.Point := ⟨1147, 1306, 500⟩
kernel_matrix step5CommonGroup27_sources : 6 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope27.sourceIndex step5CommonScope27_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope27.sourceIndex step5CommonScope27_valid a))) step5CommonPoint27 = true)
kernel_matrix step5CommonGroup27_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope27.neighborIndex step5CommonScope27_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope27.neighborIndex step5CommonScope27_valid b))) step5CommonPoint27 = true)
def step5CommonGroup27 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope27 step5CommonScope27_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint27
  (fun a => step5CommonGroup27_sources a 0) (fun b => step5CommonGroup27_neighbors b 0)

def step5CommonScope28 : Scope := ⟨38, 6, 11, 1⟩
theorem step5CommonScope28_valid : step5CommonScope28.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup28_checked : 6 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope28.sourceIndex step5CommonScope28_valid a))
    (step5CommonRawNeighbors (step5CommonScope28.neighborIndex step5CommonScope28_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope28.sourceIndex step5CommonScope28_valid a))
      (step5CommonNeighborAngles (step5CommonScope28.neighborIndex step5CommonScope28_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup28 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope28 step5CommonScope28_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup28_checked

def step5CommonScope29 : Scope := ⟨44, 7, 0, 3⟩
theorem step5CommonScope29_valid : step5CommonScope29.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup29_checked : 7 × 3 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope29.sourceIndex step5CommonScope29_valid a))
    (step5CommonRawNeighbors (step5CommonScope29.neighborIndex step5CommonScope29_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope29.sourceIndex step5CommonScope29_valid a))
      (step5CommonNeighborAngles (step5CommonScope29.neighborIndex step5CommonScope29_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup29 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope29 step5CommonScope29_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup29_checked

def step5CommonScope30 : Scope := ⟨44, 7, 3, 3⟩
theorem step5CommonScope30_valid : step5CommonScope30.Valid 51 12 := by decide +kernel

def step5CommonPoint30 : CommonPoint.Point := ⟨2332, 2675, 1000⟩
kernel_matrix step5CommonGroup30_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope30.sourceIndex step5CommonScope30_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope30.sourceIndex step5CommonScope30_valid a))) step5CommonPoint30 = true)
kernel_matrix step5CommonGroup30_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope30.neighborIndex step5CommonScope30_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope30.neighborIndex step5CommonScope30_valid b))) step5CommonPoint30 = true)
def step5CommonGroup30 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope30 step5CommonScope30_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint30
  (fun a => step5CommonGroup30_sources a 0) (fun b => step5CommonGroup30_neighbors b 0)

def step5CommonScope31 : Scope := ⟨44, 7, 6, 3⟩
theorem step5CommonScope31_valid : step5CommonScope31.Valid 51 12 := by decide +kernel

def step5CommonPoint31 : CommonPoint.Point := ⟨2318, 2647, 1000⟩
kernel_matrix step5CommonGroup31_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope31.sourceIndex step5CommonScope31_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope31.sourceIndex step5CommonScope31_valid a))) step5CommonPoint31 = true)
kernel_matrix step5CommonGroup31_neighbors : 3 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope31.neighborIndex step5CommonScope31_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope31.neighborIndex step5CommonScope31_valid b))) step5CommonPoint31 = true)
def step5CommonGroup31 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope31 step5CommonScope31_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint31
  (fun a => step5CommonGroup31_sources a 0) (fun b => step5CommonGroup31_neighbors b 0)

def step5CommonScope32 : Scope := ⟨44, 7, 9, 1⟩
theorem step5CommonScope32_valid : step5CommonScope32.Valid 51 12 := by decide +kernel

def step5CommonPoint32 : CommonPoint.Point := ⟨2304, 2631, 1000⟩
kernel_matrix step5CommonGroup32_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope32.sourceIndex step5CommonScope32_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope32.sourceIndex step5CommonScope32_valid a))) step5CommonPoint32 = true)
kernel_matrix step5CommonGroup32_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope32.neighborIndex step5CommonScope32_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope32.neighborIndex step5CommonScope32_valid b))) step5CommonPoint32 = true)
def step5CommonGroup32 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope32 step5CommonScope32_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint32
  (fun a => step5CommonGroup32_sources a 0) (fun b => step5CommonGroup32_neighbors b 0)

def step5CommonScope33 : Scope := ⟨44, 7, 10, 1⟩
theorem step5CommonScope33_valid : step5CommonScope33.Valid 51 12 := by decide +kernel

def step5CommonPoint33 : CommonPoint.Point := ⟨575, 657, 250⟩
kernel_matrix step5CommonGroup33_sources : 7 × 1 => (fun a _ =>
  CommonPoint.check (step5CommonRawSources (step5CommonScope33.sourceIndex step5CommonScope33_valid a))
    (ownKeys (step5CommonSourceAngles (step5CommonScope33.sourceIndex step5CommonScope33_valid a))) step5CommonPoint33 = true)
kernel_matrix step5CommonGroup33_neighbors : 1 × 1 => (fun b _ =>
  CommonPoint.check (step5CommonRawNeighbors (step5CommonScope33.neighborIndex step5CommonScope33_valid b))
    (ownKeys (step5CommonNeighborAngles (step5CommonScope33.neighborIndex step5CommonScope33_valid b))) step5CommonPoint33 = true)
def step5CommonGroup33 : CheckedGroup step5Sources step5Neighbors := pointGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope33 step5CommonScope33_valid
  (fun i => ownKeys (step5CommonSourceAngles i))
  (fun j => ownKeys (step5CommonNeighborAngles j)) step5CommonPoint33
  (fun a => step5CommonGroup33_sources a 0) (fun b => step5CommonGroup33_neighbors b 0)

def step5CommonScope34 : Scope := ⟨44, 7, 11, 1⟩
theorem step5CommonScope34_valid : step5CommonScope34.Valid 51 12 := by decide +kernel

kernel_matrix step5CommonGroup34_checked : 7 × 1 => (fun a b =>
  RawSupportFan.PairCheck (step5CommonRawSources (step5CommonScope34.sourceIndex step5CommonScope34_valid a))
    (step5CommonRawNeighbors (step5CommonScope34.neighborIndex step5CommonScope34_valid b))
    (fanDirectionKey (step5CommonSourceAngles (step5CommonScope34.sourceIndex step5CommonScope34_valid a))
      (step5CommonNeighborAngles (step5CommonScope34.neighborIndex step5CommonScope34_valid b))) (fun key => (key + 128) % 256))
def step5CommonGroup34 : CheckedGroup step5Sources step5Neighbors := fallbackGroup
  step5Sources step5Neighbors
  step5CommonRawSources step5CommonRawNeighbors
  step5CommonRawSources_exact step5CommonRawNeighbors_exact
  step5CommonNeighborUnblocked step5CommonScope34 step5CommonScope34_valid
  step5CommonSourceAngles step5CommonNeighborAngles
  step5CommonSourceAngles_exact step5CommonNeighborAngles_exact
  step5CommonGroup34_checked

def step5CommonScopes : List Scope := [
  step5CommonScope0, step5CommonScope1, step5CommonScope2, step5CommonScope3, step5CommonScope4, step5CommonScope5, step5CommonScope6, step5CommonScope7, step5CommonScope8, step5CommonScope9, step5CommonScope10, step5CommonScope11, step5CommonScope12, step5CommonScope13, step5CommonScope14, step5CommonScope15, step5CommonScope16, step5CommonScope17, step5CommonScope18, step5CommonScope19, step5CommonScope20, step5CommonScope21, step5CommonScope22, step5CommonScope23, step5CommonScope24, step5CommonScope25, step5CommonScope26, step5CommonScope27, step5CommonScope28, step5CommonScope29, step5CommonScope30, step5CommonScope31, step5CommonScope32, step5CommonScope33, step5CommonScope34]
def step5CommonGroups : List (CheckedGroup step5Sources step5Neighbors) := [
  step5CommonGroup0, step5CommonGroup1, step5CommonGroup2, step5CommonGroup3, step5CommonGroup4, step5CommonGroup5, step5CommonGroup6, step5CommonGroup7, step5CommonGroup8, step5CommonGroup9, step5CommonGroup10, step5CommonGroup11, step5CommonGroup12, step5CommonGroup13, step5CommonGroup14, step5CommonGroup15, step5CommonGroup16, step5CommonGroup17, step5CommonGroup18, step5CommonGroup19, step5CommonGroup20, step5CommonGroup21, step5CommonGroup22, step5CommonGroup23, step5CommonGroup24, step5CommonGroup25, step5CommonGroup26, step5CommonGroup27, step5CommonGroup28, step5CommonGroup29, step5CommonGroup30, step5CommonGroup31, step5CommonGroup32, step5CommonGroup33, step5CommonGroup34]
theorem step5CommonScopes_exact :
    step5CommonGroups.map CheckedGroup.scope = step5CommonScopes := rfl
kernel_matrix step5CommonCoverage : 51 × 12 => (fun i j =>
  ScopeCheck step5CommonScopes i.val j.val)
theorem step5_geometric_overlap (i : Fin 51) (j : Fin 12) :
    PairOverlaps (step5Sources i) (step5Neighbors j) :=
  groups_sound step5Sources step5Neighbors step5CommonGroups
    step5CommonScopes step5CommonScopes_exact step5CommonCoverage i j
#print axioms step5_geometric_overlap

end
end N12Compact.C898Cached.AllPairs
