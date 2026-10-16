import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C713.EntryPoints
import Compact.Cases.C713.RecipeInitial.All

namespace N12Compact.C713Entry
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open C713RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case713Domain0 commonPoints713 inside0 outside0 := by
  decide +kernel

def owner0_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain0, owner0, owner0_checked, owner0_premises_checked,
   C713Shared.continuousScout713Domain0_0, owner0_leaves_shared⟩

theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain0_0
      (p.square (ownerIndex p 1)) :=
  owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case713Domain1 commonPoints713 inside1 outside1 := by
  decide +kernel

def owner1_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain1, owner1, owner1_checked, owner1_premises_checked,
   C713Shared.continuousScout713Domain1_0, owner1_leaves_shared⟩

theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain1_0
      (p.square (ownerIndex p 2)) :=
  owner1_entry.sound p hf

theorem owner5_premises_checked :
    PointPremises.Check case713Domain5 commonPoints713 inside5 outside5 := by
  decide +kernel

def owner5_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain5, owner5, owner5_checked, owner5_premises_checked,
   C713Shared.continuousScout713Domain5_0, owner5_leaves_shared⟩

theorem owner5_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain5_0
      (p.square (ownerIndex p 192)) :=
  owner5_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case713Domain6 commonPoints713 inside6 outside6 := by
  decide +kernel

def owner6_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain6, owner6, owner6_checked, owner6_premises_checked,
   C713Shared.continuousScout713Domain6_0, owner6_leaves_shared⟩

theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain6_0
      (p.square (ownerIndex p 512)) :=
  owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case713Domain7 commonPoints713 inside7 outside7 := by
  decide +kernel

def owner7_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain7, owner7, owner7_checked, owner7_premises_checked,
   C713Shared.continuousScout713Domain7_0, owner7_leaves_shared⟩

theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain7_0
      (p.square (ownerIndex p 2304)) :=
  owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case713Domain8 commonPoints713 inside8 outside8 := by
  decide +kernel

def owner8_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain8, owner8, owner8_checked, owner8_premises_checked,
   C713Shared.continuousScout713Domain8_0, owner8_leaves_shared⟩

theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain8_0
      (p.square (ownerIndex p 4096)) :=
  owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case713Domain9 commonPoints713 inside9 outside9 := by
  decide +kernel

def owner9_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain9, owner9, owner9_checked, owner9_premises_checked,
   C713Shared.continuousScout713Domain9_0, owner9_leaves_shared⟩

theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain9_0
      (p.square (ownerIndex p 8192)) :=
  owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case713Domain10 commonPoints713 inside10 outside10 := by
  decide +kernel

def owner10_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain10, owner10, owner10_checked, owner10_premises_checked,
   C713Shared.continuousScout713Domain10_0, owner10_leaves_shared⟩

theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain10_0
      (p.square (ownerIndex p 16384)) :=
  owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case713Domain11 commonPoints713 inside11 outside11 := by
  decide +kernel

def owner11_entry : CertifiedOwner case713Family commonPoints713 :=
  ⟨case713Domain11, owner11, owner11_checked, owner11_premises_checked,
   C713Shared.continuousScout713Domain11_0, owner11_leaves_shared⟩

theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case713Family) :
    OrientedPoseCovered C713Shared.continuousScout713Domain11_0
      (p.square (ownerIndex p 32768)) :=
  owner11_entry.sound p hf


end
end N12Compact.C713Entry
