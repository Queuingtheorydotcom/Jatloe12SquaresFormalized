import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C717.EntryPoints
import Compact.Cases.C717.RecipeInitial.Owner00
import Compact.Cases.C717.RecipeInitial.Owner01
import Compact.Cases.C717.RecipeInitial.Owner02
import Compact.Cases.C717.RecipeInitial.Owner03
import Compact.Cases.C717.RecipeInitial.Owner04
import Compact.Cases.C717.RecipeInitial.Owner06
import Compact.Cases.C717.RecipeInitial.Owner07
import Compact.Cases.C717.RecipeInitial.Owner08
import Compact.Cases.C717.RecipeInitial.Owner09
import Compact.Cases.C717.RecipeInitial.Owner10
import Compact.Cases.C717.RecipeInitial.Owner11

namespace N12Compact.C717Entry
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover C717RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case717Domain0 commonPoints717 inside0 outside0 := by
  decide +kernel

def owner0_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain0, owner0, owner0_checked, owner0_premises_checked,
   Preservation.C717.continuousScout717Domain0_0, owner0_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain0_0 (p.square (ownerIndex p 1)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case717Domain1 commonPoints717 inside1 outside1 := by
  decide +kernel

def owner1_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain1, owner1, owner1_checked, owner1_premises_checked,
   Preservation.C717.continuousScout717Domain1_0, owner1_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain1_0 (p.square (ownerIndex p 2)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner1_entry.sound p hf

theorem owner2_premises_checked :
    PointPremises.Check case717Domain2 commonPoints717 inside2 outside2 := by
  decide +kernel

def owner2_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain2, owner2, owner2_checked, owner2_premises_checked,
   Preservation.C717.continuousScout717Domain2_0, owner2_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner2_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain2_0 (p.square (ownerIndex p 12)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner2_entry.sound p hf

theorem owner3_premises_checked :
    PointPremises.Check case717Domain3 commonPoints717 inside3 outside3 := by
  decide +kernel

def owner3_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain3, owner3, owner3_checked, owner3_premises_checked,
   Preservation.C717.continuousScout717Domain3_0, owner3_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner3_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain3_0 (p.square (ownerIndex p 16)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner3_entry.sound p hf

theorem owner4_premises_checked :
    PointPremises.Check case717Domain4 commonPoints717 inside4 outside4 := by
  decide +kernel

def owner4_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain4, owner4, owner4_checked, owner4_premises_checked,
   Preservation.C717.continuousScout717Domain4_0, owner4_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner4_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain4_0 (p.square (ownerIndex p 32)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner4_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case717Domain6 commonPoints717 inside6 outside6 := by
  decide +kernel

def owner6_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain6, owner6, owner6_checked, owner6_premises_checked,
   Preservation.C717.continuousScout717Domain6_0, owner6_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain6_0 (p.square (ownerIndex p 768)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case717Domain7 commonPoints717 inside7 outside7 := by
  decide +kernel

def owner7_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain7, owner7, owner7_checked, owner7_premises_checked,
   Preservation.C717.continuousScout717Domain7_0, owner7_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain7_0 (p.square (ownerIndex p 3072)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case717Domain8 commonPoints717 inside8 outside8 := by
  decide +kernel

def owner8_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain8, owner8, owner8_checked, owner8_premises_checked,
   Preservation.C717.continuousScout717Domain8_0, owner8_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain8_0 (p.square (ownerIndex p 4096)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case717Domain9 commonPoints717 inside9 outside9 := by
  decide +kernel

def owner9_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain9, owner9, owner9_checked, owner9_premises_checked,
   Preservation.C717.continuousScout717Domain9_0, owner9_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain9_0 (p.square (ownerIndex p 8192)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case717Domain10 commonPoints717 inside10 outside10 := by
  decide +kernel

def owner10_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain10, owner10, owner10_checked, owner10_premises_checked,
   Preservation.C717.continuousScout717Domain10_0, owner10_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain10_0 (p.square (ownerIndex p 16384)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case717Domain11 commonPoints717 inside11 outside11 := by
  decide +kernel

def owner11_entry : CertifiedOwner case717Family commonPoints717 :=
  ⟨case717Domain11, owner11, owner11_checked, owner11_premises_checked,
   Preservation.C717.continuousScout717Domain11_0, owner11_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C717.family) :
    OrientedPoseCovered Preservation.C717.continuousScout717Domain11_0 (p.square (ownerIndex p 32768)) := by
  change codedMarkerFamily p = case717Family at hf
  exact owner11_entry.sound p hf


end
end N12Compact.C717Entry
