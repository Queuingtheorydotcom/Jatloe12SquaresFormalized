import Compact.Completion.OtherCases.C983.Components06.FQueries

/-! Literal data and ordinary kernel checks split at reusable component cuts. -/
namespace N12Compact.Completion.OtherCases.C983.Component06Data
open S12 S12Pilot
open N12Compact.Completion.OtherCases.MonotoneQueries
set_option Elab.async false
noncomputable section

def fSingle6 : SingleDomain :=
  ⟨1024,1,3,[{5},{7},{9},{3,5},{4,5},{4,9},{5,7},{5,8},{5,9},{7,9},{8,9},{0,4,5},{0,4,9},{1,4,5},{3,4,5},{3,5,7},{3,5,8},{3,5,9},{4,5,7},{4,5,8},{4,5,9},{4,7,9},{4,8,9},{5,7,8},{5,7,9},{5,8,9},{7,8,9}],fQueries6⟩

theorem fChecked6 :
    fSingle6.Check family 0 fSignatures6 := by decide +kernel

end
end N12Compact.Completion.OtherCases.C983.Component06Data
