import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C701.EntryPoints
import Compact.Cases.C701.RecipeInitial.Owner00
import Compact.Cases.C701.RecipeInitial.Owner01
import Compact.Cases.C701.RecipeInitial.Owner02
import Compact.Cases.C701.RecipeInitial.Owner03
import Compact.Cases.C701.RecipeInitial.Owner04
import Compact.Cases.C701.RecipeInitial.Owner05
import Compact.Cases.C701.RecipeInitial.Owner06
import Compact.Cases.C701.RecipeInitial.Owner07
import Compact.Cases.C701.RecipeInitial.Owner08
import Compact.Cases.C701.RecipeInitial.Owner09
import Compact.Cases.C701.RecipeInitial.Owner10
import Compact.Cases.C701.RecipeInitial.Owner11

namespace N12Compact.C701Entry
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover C701RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case701Domain0 commonPoints701 inside0 outside0 := by
  decide +kernel

def owner0_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain0, owner0, owner0_checked, owner0_premises_checked,
   Preservation.C701.continuousScout701Domain0_0, owner0_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain0_0 (p.square (ownerIndex p 1)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case701Domain1 commonPoints701 inside1 outside1 := by
  decide +kernel

def owner1_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain1, owner1, owner1_checked, owner1_premises_checked,
   Preservation.C701.continuousScout701Domain1_0, owner1_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain1_0 (p.square (ownerIndex p 2)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner1_entry.sound p hf

theorem owner2_premises_checked :
    PointPremises.Check case701Domain2 commonPoints701 inside2 outside2 := by
  decide +kernel

def owner2_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain2, owner2, owner2_checked, owner2_premises_checked,
   Preservation.C701.continuousScout701Domain2_0, owner2_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner2_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain2_0 (p.square (ownerIndex p 12)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner2_entry.sound p hf

theorem owner3_premises_checked :
    PointPremises.Check case701Domain3 commonPoints701 inside3 outside3 := by
  decide +kernel

def owner3_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain3, owner3, owner3_checked, owner3_premises_checked,
   Preservation.C701.continuousScout701Domain3_0, owner3_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner3_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain3_0 (p.square (ownerIndex p 16)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner3_entry.sound p hf

theorem owner4_premises_checked :
    PointPremises.Check case701Domain4 commonPoints701 inside4 outside4 := by
  decide +kernel

def owner4_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain4, owner4, owner4_checked, owner4_premises_checked,
   Preservation.C701.continuousScout701Domain4_0, owner4_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner4_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain4_0 (p.square (ownerIndex p 32)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner4_entry.sound p hf

theorem owner5_premises_checked :
    PointPremises.Check case701Domain5 commonPoints701 inside5 outside5 := by
  decide +kernel

def owner5_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain5, owner5, owner5_checked, owner5_premises_checked,
   Preservation.C701.continuousScout701Domain5_0, owner5_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner5_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain5_0 (p.square (ownerIndex p 192)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner5_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case701Domain6 commonPoints701 inside6 outside6 := by
  decide +kernel

def owner6_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain6, owner6, owner6_checked, owner6_premises_checked,
   Preservation.C701.continuousScout701Domain6_0, owner6_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain6_0 (p.square (ownerIndex p 256)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case701Domain7 commonPoints701 inside7 outside7 := by
  decide +kernel

def owner7_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain7, owner7, owner7_checked, owner7_premises_checked,
   Preservation.C701.continuousScout701Domain7_0, owner7_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain7_0 (p.square (ownerIndex p 1536)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case701Domain8 commonPoints701 inside8 outside8 := by
  decide +kernel

def owner8_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain8, owner8, owner8_checked, owner8_premises_checked,
   Preservation.C701.continuousScout701Domain8_0, owner8_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain8_0 (p.square (ownerIndex p 4096)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case701Domain9 commonPoints701 inside9 outside9 := by
  decide +kernel

def owner9_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain9, owner9, owner9_checked, owner9_premises_checked,
   Preservation.C701.continuousScout701Domain9_0, owner9_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain9_0 (p.square (ownerIndex p 8192)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case701Domain10 commonPoints701 inside10 outside10 := by
  decide +kernel

def owner10_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain10, owner10, owner10_checked, owner10_premises_checked,
   Preservation.C701.continuousScout701Domain10_0, owner10_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain10_0 (p.square (ownerIndex p 16384)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case701Domain11 commonPoints701 inside11 outside11 := by
  decide +kernel

def owner11_entry : CertifiedOwner case701Family commonPoints701 :=
  ⟨case701Domain11, owner11, owner11_checked, owner11_premises_checked,
   Preservation.C701.continuousScout701Domain11_0, owner11_leaves_shared⟩

/-- Exactly the original graph's unconditional packing entrance. -/
theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = Preservation.C701.family) :
    OrientedPoseCovered Preservation.C701.continuousScout701Domain11_0 (p.square (ownerIndex p 34816)) := by
  change codedMarkerFamily p = case701Family at hf
  exact owner11_entry.sound p hf


end
end N12Compact.C701Entry
