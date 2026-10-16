import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C979.EntryPoints
import Compact.Cases.C979.RecipeInitial.Owner00
import Compact.Cases.C979.RecipeInitial.Owner01
import Compact.Cases.C979.RecipeInitial.Owner02
import Compact.Cases.C979.RecipeInitial.Owner03
import Compact.Cases.C979.RecipeInitial.Owner04
import Compact.Cases.C979.RecipeInitial.Owner05
import Compact.Cases.C979.RecipeInitial.Owner06
import Compact.Cases.C979.RecipeInitial.Owner07
import Compact.Cases.C979.RecipeInitial.Owner08
import Compact.Cases.C979.RecipeInitial.Owner09
import Compact.Cases.C979.RecipeInitial.Owner10
import Compact.Cases.C979.RecipeInitial.Owner11

namespace N12Compact.C979Entry
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover C979RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case979Domain0 commonPoints979 inside0 outside0 := by
  decide +kernel

def owner0_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain0, owner0, owner0_checked, owner0_premises_checked,
   Preservation.C979.continuousScout979Domain0_0, owner0_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain0_0 (p.square (ownerIndex p 1)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case979Domain1 commonPoints979 inside1 outside1 := by
  decide +kernel

def owner1_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain1, owner1, owner1_checked, owner1_premises_checked,
   Preservation.C979.continuousScout979Domain1_0, owner1_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain1_0 (p.square (ownerIndex p 2)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner1_entry.sound p hf

theorem owner2_premises_checked :
    PointPremises.Check case979Domain2 commonPoints979 inside2 outside2 := by
  decide +kernel

def owner2_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain2, owner2, owner2_checked, owner2_premises_checked,
   Preservation.C979.continuousScout979Domain2_0, owner2_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner2_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain2_0 (p.square (ownerIndex p 12)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner2_entry.sound p hf

theorem owner3_premises_checked :
    PointPremises.Check case979Domain3 commonPoints979 inside3 outside3 := by
  decide +kernel

def owner3_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain3, owner3, owner3_checked, owner3_premises_checked,
   Preservation.C979.continuousScout979Domain3_0, owner3_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner3_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain3_0 (p.square (ownerIndex p 48)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner3_entry.sound p hf

theorem owner4_premises_checked :
    PointPremises.Check case979Domain4 commonPoints979 inside4 outside4 := by
  decide +kernel

def owner4_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain4, owner4, owner4_checked, owner4_premises_checked,
   Preservation.C979.continuousScout979Domain4_0, owner4_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner4_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain4_0 (p.square (ownerIndex p 192)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner4_entry.sound p hf

theorem owner5_premises_checked :
    PointPremises.Check case979Domain5 commonPoints979 inside5 outside5 := by
  decide +kernel

def owner5_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain5, owner5, owner5_checked, owner5_premises_checked,
   Preservation.C979.continuousScout979Domain5_0, owner5_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner5_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain5_0 (p.square (ownerIndex p 256)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner5_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case979Domain6 commonPoints979 inside6 outside6 := by
  decide +kernel

def owner6_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain6, owner6, owner6_checked, owner6_premises_checked,
   Preservation.C979.continuousScout979Domain6_0, owner6_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain6_0 (p.square (ownerIndex p 512)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case979Domain7 commonPoints979 inside7 outside7 := by
  decide +kernel

def owner7_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain7, owner7, owner7_checked, owner7_premises_checked,
   Preservation.C979.continuousScout979Domain7_0, owner7_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain7_0 (p.square (ownerIndex p 3072)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case979Domain8 commonPoints979 inside8 outside8 := by
  decide +kernel

def owner8_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain8, owner8, owner8_checked, owner8_premises_checked,
   Preservation.C979.continuousScout979Domain8_0, owner8_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain8_0 (p.square (ownerIndex p 4096)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case979Domain9 commonPoints979 inside9 outside9 := by
  decide +kernel

def owner9_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain9, owner9, owner9_checked, owner9_premises_checked,
   Preservation.C979.continuousScout979Domain9_0, owner9_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain9_0 (p.square (ownerIndex p 8192)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case979Domain10 commonPoints979 inside10 outside10 := by
  decide +kernel

def owner10_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain10, owner10, owner10_checked, owner10_premises_checked,
   Preservation.C979.continuousScout979Domain10_0, owner10_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain10_0 (p.square (ownerIndex p 16384)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case979Domain11 commonPoints979 inside11 outside11 := by
  decide +kernel

def owner11_entry : CertifiedOwner case979Family commonPoints979 :=
  ⟨case979Domain11, owner11, owner11_checked, owner11_premises_checked,
   Preservation.C979.continuousScout979Domain11_0, owner11_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C979.family) :
    OrientedPoseCovered Preservation.C979.continuousScout979Domain11_0 (p.square (ownerIndex p 32768)) := by
  change codedMarkerFamily p = case979Family at hf
  exact owner11_entry.sound p hf


end
end N12Compact.C979Entry
