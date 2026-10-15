import S12.CompactFarkasText
import S12.ContinuousCertificate
namespace S12
set_option autoImplicit false

/-- A compact data representation, not a new proof rule. The existing checks
still compare these exact decoded constraints with the complete source leaves. -/
def decodeSignedRational (text : String) : ℚ :=
  if text.startsWith "-" then -decodeFarkasWeight (text.drop 1)
  else decodeFarkasWeight text

def regionConstraintsFromText (text : String) : RegionConstraints :=
  if text.isEmpty then [] else
  (text.splitOn ";").map (fun row =>
    let fields := row.splitOn ","
    let x := decodeSignedRational ((fields[0]?).getD "0")
    let y := decodeSignedRational ((fields[1]?).getD "0")
    let z := decodeSignedRational ((fields[2]?).getD "0")
    ⟨⟨![x,y],z⟩,(fields[3]?).getD "0"=="1"⟩)
end S12
