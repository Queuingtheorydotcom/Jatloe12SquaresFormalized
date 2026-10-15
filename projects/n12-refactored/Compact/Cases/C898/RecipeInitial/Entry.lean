import Compact.Bridge.DirectOwnerFamily
import Compact.Cases.C898.EntryPoints
import Compact.Cases.C898.RecipeInitial.All

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898Entry
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

open C898RecipeInitial

theorem owner0_premises_checked :
    PointPremises.Check case898Domain0 commonPoints898 inside0 outside0 := by
  decide +kernel

noncomputable def owner0_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain0, owner0, owner0_checked, owner0_premises_checked,
   C898Shared.continuousScout898Domain0_0, owner0_leaves_shared⟩

theorem owner0_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain0_0
      (p.square (ownerIndex p 1)) :=
  owner0_entry.sound p hf

theorem owner1_premises_checked :
    PointPremises.Check case898Domain1 commonPoints898 inside1 outside1 := by
  decide +kernel

noncomputable def owner1_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain1, owner1, owner1_checked, owner1_premises_checked,
   C898Shared.continuousScout898Domain1_0, owner1_leaves_shared⟩

theorem owner1_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain1_0
      (p.square (ownerIndex p 2)) :=
  owner1_entry.sound p hf

theorem owner2_premises_checked :
    PointPremises.Check case898Domain2 commonPoints898 inside2 outside2 := by
  decide +kernel

noncomputable def owner2_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain2, owner2, owner2_checked, owner2_premises_checked,
   C898Shared.continuousScout898Domain2_0, owner2_leaves_shared⟩

theorem owner2_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain2_0
      (p.square (ownerIndex p 12)) :=
  owner2_entry.sound p hf

theorem owner3_premises_checked :
    PointPremises.Check case898Domain3 commonPoints898 inside3 outside3 := by
  decide +kernel

noncomputable def owner3_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain3, owner3, owner3_checked, owner3_premises_checked,
   C898Shared.continuousScout898Domain3_0, owner3_leaves_shared⟩

theorem owner3_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain3_0
      (p.square (ownerIndex p 16)) :=
  owner3_entry.sound p hf

theorem owner5_premises_checked :
    PointPremises.Check case898Domain5 commonPoints898 inside5 outside5 := by
  decide +kernel

noncomputable def owner5_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain5, owner5, owner5_checked, owner5_premises_checked,
   C898Shared.continuousScout898Domain5_0, owner5_leaves_shared⟩

theorem owner5_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain5_0
      (p.square (ownerIndex p 768)) :=
  owner5_entry.sound p hf

theorem owner6_premises_checked :
    PointPremises.Check case898Domain6 commonPoints898 inside6 outside6 := by
  decide +kernel

noncomputable def owner6_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain6, owner6, owner6_checked, owner6_premises_checked,
   C898Shared.continuousScout898Domain6_0, owner6_leaves_shared⟩

theorem owner6_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain6_0
      (p.square (ownerIndex p 1056)) :=
  owner6_entry.sound p hf

theorem owner7_premises_checked :
    PointPremises.Check case898Domain7 commonPoints898 inside7 outside7 := by
  decide +kernel

noncomputable def owner7_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain7, owner7, owner7_checked, owner7_premises_checked,
   C898Shared.continuousScout898Domain7_0, owner7_leaves_shared⟩

theorem owner7_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain7_0
      (p.square (ownerIndex p 2048)) :=
  owner7_entry.sound p hf

theorem owner8_premises_checked :
    PointPremises.Check case898Domain8 commonPoints898 inside8 outside8 := by
  decide +kernel

noncomputable def owner8_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain8, owner8, owner8_checked, owner8_premises_checked,
   C898Shared.continuousScout898Domain8_0, owner8_leaves_shared⟩

theorem owner8_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain8_0
      (p.square (ownerIndex p 4096)) :=
  owner8_entry.sound p hf

theorem owner9_premises_checked :
    PointPremises.Check case898Domain9 commonPoints898 inside9 outside9 := by
  decide +kernel

noncomputable def owner9_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain9, owner9, owner9_checked, owner9_premises_checked,
   C898Shared.continuousScout898Domain9_0, owner9_leaves_shared⟩

theorem owner9_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain9_0
      (p.square (ownerIndex p 8192)) :=
  owner9_entry.sound p hf

theorem owner10_premises_checked :
    PointPremises.Check case898Domain10 commonPoints898 inside10 outside10 := by
  decide +kernel

noncomputable def owner10_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain10, owner10, owner10_checked, owner10_premises_checked,
   C898Shared.continuousScout898Domain10_0, owner10_leaves_shared⟩

theorem owner10_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain10_0
      (p.square (ownerIndex p 16384)) :=
  owner10_entry.sound p hf

theorem owner11_premises_checked :
    PointPremises.Check case898Domain11 commonPoints898 inside11 outside11 := by
  decide +kernel

noncomputable def owner11_entry : CertifiedOwner case898Family commonPoints898 :=
  ⟨case898Domain11, owner11, owner11_checked, owner11_premises_checked,
   C898Shared.continuousScout898Domain11_0, owner11_leaves_shared⟩

theorem owner11_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) :
    OrientedPoseCovered C898Shared.continuousScout898Domain11_0
      (p.square (ownerIndex p 32768)) :=
  owner11_entry.sound p hf


end N12Compact.C898Entry
