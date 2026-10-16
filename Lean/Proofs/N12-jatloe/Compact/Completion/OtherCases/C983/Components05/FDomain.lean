import Compact.Completion.OtherCases.C983.Components05.FQueries

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component05Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def fSingle5 : SingleDomain :=
  ⟨512,1,3,[{4},{6},{8},{2,4},{4,5},{4,6},{4,8},{4,9},{5,8},{6,8},{8,9},{0,4,5},{1,4,5},{1,5,8},{2,4,5},{2,4,6},{2,4,8},{2,4,9},{4,5,6},{4,5,8},{4,5,9},{4,6,8},{4,6,9},{4,8,9},{5,6,8},{5,8,9},{6,8,9}],fQueries5⟩

theorem fChecked5 :
    fSingle5.Check family 0 fSignatures5 := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component05Data
