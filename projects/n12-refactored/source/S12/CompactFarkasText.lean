import S12.IndexedFarkas
namespace S12
set_option autoImplicit false

/-- Decimal nonnegative rational data. The format is only a space-saving
encoding: all decoded weights still face the full certificate check. -/
def decodeFarkasWeight (text : String) : ℚ :=
  let parts := text.splitOn "/"
  let num := ((parts[0]?).getD "0").toNat?.getD 0
  let den := ((parts[1]?).getD "1").toNat?.getD 0
  (num:ℚ)/(den:ℚ)

def decodeFarkasProofs (text : String) : List (List (ℚ × Nat)) :=
  (text.splitOn ";").map (fun proof =>
    (proof.splitOn ",").map (fun term =>
      let pair := term.splitOn ":"
      (decodeFarkasWeight ((pair[0]?).getD "0"),((pair[1]?).getD "0").toNat?.getD 0)))

def expandImplicationText {n : Nat} (inputs targets : List (LinearConstraint n))
    (text : String) : List (List (ℚ × LinearConstraint n)) :=
  expandImplicationIndices inputs targets (decodeFarkasProofs text)

/-- No correctness premise about the text encoding or its producer is needed.
The mathematical check is applied to the decoded objects themselves. -/
theorem compact_text_implications_sound {n : Nat} (inputs targets : List (LinearConstraint n))
    (text : String) (hw : IndexedImplications inputs targets (expandImplicationText inputs targets text)) :
    ∀ target∈targets,∃ terms∈expandImplicationText inputs targets text,
      LinearImplicationCheck inputs target terms :=
  indexed_implications_sound inputs targets _ hw

#print axioms compact_text_implications_sound
end S12
