import Compact.Completion.OtherCases.C1090.OriginalData
import Compact.Completion.OtherCases.C1090.StructuralReduction

/-! The new C1090 continuous proof applied to its original marker family.
The sole premise beyond the actual packing/family is AuxiliaryEntrance;
its genuine finite producer is still required. No C1089 family exclusion,
reported catalogue count or unprovided replay file is used. This conditional
join does not register an ExcludesCase1090 theorem. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.OriginalData
open S12 S12Pilot
set_option Elab.async false

theorem impossible_of_auxiliary_entrance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (h : AuxiliaryEntrance (owners p)) : False :=
  Structural.impossible_of_early_input (owners p) (early_input p hf h)

#print axioms impossible_of_auxiliary_entrance
end N12Compact.Completion.OtherCases.C1090.OriginalData
