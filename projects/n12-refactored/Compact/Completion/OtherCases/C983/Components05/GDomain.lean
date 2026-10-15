import Compact.Completion.OtherCases.C983.Components05.GQueries

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component05Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def gSingle5 : SingleDomain :=
  ⟨512,1,2,[{5},{6},{8},{2,5},{2,6},{3,5},{3,6},{5,6},{5,8},{6,8},{6,9}],gQueries5⟩

theorem gChecked5 :
    gSingle5.Check family 1 gSignatures5 := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component05Data
