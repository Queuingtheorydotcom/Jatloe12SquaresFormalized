import S12.CompactPoseText
import S12.PoseRegion
namespace S12
set_option autoImplicit false

/-- Decoding supplies data only. `RegionTree.Check`, `RegionTree.leaves`, and
the complete incoming-cover checks apply to the decoded tree itself. Neither
the external encoder nor the intended meaning of the text is assumed. -/
def farkasTermsFromText (text : String) : FarkasTerms :=
  if text.isEmpty then [] else
  (text.splitOn ";").map (fun row =>
    let fields := row.splitOn ","
    let weight := decodeSignedRational ((fields[0]?).getD "0")
    let x := decodeSignedRational ((fields[1]?).getD "0")
    let y := decodeSignedRational ((fields[2]?).getD "0")
    let z := decodeSignedRational ((fields[3]?).getD "0")
    (weight,⟨⟨![x,y],z⟩,(fields[4]?).getD "0"=="1"⟩))

def appendRegionTreeRecord (nodes : Array RegionTree) (row : String) : Array RegionTree :=
  let fields := row.splitOn "|"
  let tag := (fields[0]?).getD "L"
  let getTree := fun (k : Nat) =>
    (nodes[(((fields[k]?).getD "0").toNat?).getD 0]?).getD .leaf
  let tree := if tag=="E" then
      RegionTree.empty (farkasTermsFromText ((fields[1]?).getD ""))
    else if tag=="C" then
      let test := ((regionConstraintsFromText ((fields[1]?).getD ""))[0]?).getD
        ⟨⟨![0,0],0⟩,false⟩
      RegionTree.cut test (getTree 2) (getTree 3)
    else if tag=="F" then
      RegionTree.forbidden (regionConstraintsFromText ((fields[1]?).getD ""))
        ((((fields[2]?).getD "").splitOn "~").map farkasTermsFromText)
    else RegionTree.leaf
  nodes.push tree

def regionTreeFromText (text : String) : RegionTree :=
  let nodes := (text.splitOn "\n").foldl appendRegionTreeRecord #[]
  (nodes[nodes.size-1]?).getD .leaf

theorem compact_region_tree_sound (text : String) (inputs : RegionConstraints)
    (forbidden : List RegionConstraints)
    (hc : (regionTreeFromText text).Check inputs forbidden)
    (x : Fin 2→ℝ) (hx : ∀ r∈inputs,r.Holds x)
    (hf : ∀ block∈forbidden,¬(∀ r∈block,r.Holds x)) :
    ∃ leaf∈(regionTreeFromText text).leaves inputs,∀ r∈leaf,r.Holds x :=
  RegionTree.sound _ _ _ hc x hx hf

#print axioms compact_region_tree_sound
end S12
