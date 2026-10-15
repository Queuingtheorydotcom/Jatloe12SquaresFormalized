import Compact.Completion.OtherCases.C983.Components06.GQueries

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component06Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def gSingle6 : SingleDomain :=
  ⟨1024,1,2,[{6},{7},{9},{3,6},{3,7},{4,6},{4,7},{6,7},{6,8},{6,9},{7,9}],gQueries6⟩

theorem gChecked6 :
    gSingle6.Check family 1 gSignatures6 := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component06Data
