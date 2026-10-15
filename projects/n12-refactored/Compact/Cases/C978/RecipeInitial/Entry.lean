import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C978.EntryPoints
import Compact.Cases.C978.RecipeInitial.Owner00
import Compact.Cases.C978.RecipeInitial.Owner01
import Compact.Cases.C978.RecipeInitial.Owner05
import Compact.Cases.C978.RecipeInitial.Owner06
import Compact.Cases.C978.RecipeInitial.Owner07
import Compact.Cases.C978.RecipeInitial.Owner08
import Compact.Cases.C978.RecipeInitial.Owner09
import Compact.Cases.C978.RecipeInitial.Owner10
import Compact.Cases.C978.RecipeInitial.Owner11

namespace N12Compact.C978Entry
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover C978RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case978Domain0 commonPoints978 inside0 outside0 := by
  decide +kernel

def owner0_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain0, owner0, owner0_checked, owner0_premises_checked,
   Preservation.C978.continuousScout978Domain0_0, owner0_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain0_0 (p.square (ownerIndex p 1)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case978Domain1 commonPoints978 inside1 outside1 := by
  decide +kernel

def owner1_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain1, owner1, owner1_checked, owner1_premises_checked,
   Preservation.C978.continuousScout978Domain1_0, owner1_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain1_0 (p.square (ownerIndex p 2)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner1_entry.sound p hf

theorem owner5_premises_checked :
    PointPremises.Check case978Domain5 commonPoints978 inside5 outside5 := by
  decide +kernel

def owner5_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain5, owner5, owner5_checked, owner5_premises_checked,
   Preservation.C978.continuousScout978Domain5_0, owner5_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner5_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain5_0 (p.square (ownerIndex p 256)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner5_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case978Domain6 commonPoints978 inside6 outside6 := by
  decide +kernel

def owner6_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain6, owner6, owner6_checked, owner6_premises_checked,
   Preservation.C978.continuousScout978Domain6_0, owner6_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain6_0 (p.square (ownerIndex p 512)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case978Domain7 commonPoints978 inside7 outside7 := by
  decide +kernel

def owner7_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain7, owner7, owner7_checked, owner7_premises_checked,
   Preservation.C978.continuousScout978Domain7_0, owner7_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain7_0 (p.square (ownerIndex p 2048)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case978Domain8 commonPoints978 inside8 outside8 := by
  decide +kernel

def owner8_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain8, owner8, owner8_checked, owner8_premises_checked,
   Preservation.C978.continuousScout978Domain8_0, owner8_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain8_0 (p.square (ownerIndex p 4096)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case978Domain9 commonPoints978 inside9 outside9 := by
  decide +kernel

def owner9_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain9, owner9, owner9_checked, owner9_premises_checked,
   Preservation.C978.continuousScout978Domain9_0, owner9_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain9_0 (p.square (ownerIndex p 8192)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case978Domain10 commonPoints978 inside10 outside10 := by
  decide +kernel

def owner10_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain10, owner10, owner10_checked, owner10_premises_checked,
   Preservation.C978.continuousScout978Domain10_0, owner10_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain10_0 (p.square (ownerIndex p 16384)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case978Domain11 commonPoints978 inside11 outside11 := by
  decide +kernel

def owner11_entry : CertifiedOwner case978Family commonPoints978 :=
  ⟨case978Domain11, owner11, owner11_checked, owner11_premises_checked,
   Preservation.C978.continuousScout978Domain11_0, owner11_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C978.family) :
    OrientedPoseCovered Preservation.C978.continuousScout978Domain11_0 (p.square (ownerIndex p 33792)) := by
  change codedMarkerFamily p = case978Family at hf
  exact owner11_entry.sound p hf


end
end N12Compact.C978Entry
