import Compact.Bridge.OwnerSegmentCrossing

/-! Literal strict segment intersections, shared across the five cases. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerSegmentCrossing

def crossing0 : OwnerSegmentCrossing.Data :=
  ⟨512,17408,{8,16},{5,18},
    (47/20,33/20),(3,87/50),(47/20,47/20),(3,8/5), 5/6, 5/6⟩

theorem crossing0_inputs : crossing0.InputCheck := by decide +kernel
theorem crossing0_checked : crossing0.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing0]

def crossing1 : OwnerSegmentCrossing.Data :=
  ⟨2048,33792,{5,14},{3,16},
    (33/20,47/20),(87/50,3),(47/20,47/20),(8/5,3), 5/6, 5/6⟩

theorem crossing1_inputs : crossing1.InputCheck := by decide +kernel
theorem crossing1_checked : crossing1.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing1]

def crossing2 : OwnerSegmentCrossing.Data :=
  ⟨512,34816,{8,16},{3,18},
    (47/20,33/20),(3,87/50),(33/20,47/20),(3,8/5), 20/29, 74/87⟩

theorem crossing2_inputs : crossing2.InputCheck := by decide +kernel
theorem crossing2_checked : crossing2.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing2]

def crossing3 : OwnerSegmentCrossing.Data :=
  ⟨17408,34816,{5,14},{3,16},
    (47/20,47/20),(2,113/50),(2,1543/500),(113/50,2), 9437/20175, 2891/4035⟩

theorem crossing3_inputs : crossing3.InputCheck := by decide +kernel
theorem crossing3_checked : crossing3.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing3]

def crossing4 : OwnerSegmentCrossing.Data :=
  ⟨256,6144,{4,13},{1,18},
    (33/20,33/20),(87/50,2),(457/500,2),(3,8/5), 4357/7661, 2891/7661⟩

theorem crossing4_inputs : crossing4.InputCheck := by decide +kernel
theorem crossing4_checked : crossing4.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing4]

def crossing5 : OwnerSegmentCrossing.Data :=
  ⟨256,6144,{4,13},{1,16},
    (33/20,33/20),(87/50,2),(457/500,2),(113/50,2), 1, 413/673⟩

theorem crossing5_inputs : crossing5.InputCheck := by decide +kernel
theorem crossing5_checked : crossing5.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing5]

def crossing6 : OwnerSegmentCrossing.Data :=
  ⟨512,8448,{4,15},{6,13},
    (47/20,33/20),(113/50,1),(33/20,33/20),(12/5,1), 5/6, 5/6⟩

theorem crossing6_inputs : crossing6.InputCheck := by decide +kernel
theorem crossing6_checked : crossing6.CrossCheck := by
  norm_num [OwnerSegmentCrossing.Data.CrossCheck, crossing6]

end N12Compact.FourSquareHighRightCases
