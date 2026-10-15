import Compact.Bridge.C1092WallCycle
import S12.FamilyTransport

/-! Owner, wall, central and Boolean actions for the original C1092 family.
All declarations retain their original namespace and values. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

def ownerX : Fin 12 → Fin 12 := ![1,0,3,2,5,4,7,6,10,9,8,11]
def ownerY : Fin 12 → Fin 12 := ![3,2,1,0,7,6,5,4,8,11,10,9]
def ownerSwap : Fin 12 → Fin 12 := ![0,3,2,1,4,7,6,5,9,8,11,10]

/-- New owner i comes from this old owner; this follows the existing
`Transform.apply` convention, rather than a guessed forward rotation. -/
def ownerAction (g : Transform) (i : Fin 12) : Fin 12 :=
  let j := if g.swap then ownerSwap i else i
  let k := if g.reflectY then ownerY j else j
  if g.reflectX then ownerX k else k

def wallX : Fin 4 → Fin 4 := ![2,1,0,3]
def wallY : Fin 4 → Fin 4 := ![0,3,2,1]
def wallSwap : Fin 4 → Fin 4 := ![1,0,3,2]

def wallAction (g : Transform) (i : Fin 4) : Fin 4 :=
  let j := if g.swap then wallSwap i else i
  let k := if g.reflectY then wallY j else j
  if g.reflectX then wallX k else k

def centralX : Fin 4 → Fin 4 := ![1,0,3,2]
def centralY : Fin 4 → Fin 4 := ![3,2,1,0]
def centralSwap : Fin 4 → Fin 4 := ![0,3,2,1]

def centralAction (g : Transform) (i : Fin 4) : Fin 4 :=
  let j := if g.swap then centralSwap i else i
  let k := if g.reflectY then centralY j else j
  if g.reflectX then centralX k else k

theorem ownerAction_wall (g : Transform) (k : Fin 4) :
    ownerAction g (wallOwner k) = wallOwner (wallAction g k) := by
  rcases g with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> fin_cases k <;> rfl

theorem ownerAction_central (g : Transform) (k : Fin 4) :
    ownerAction g (centralOwner k) = centralOwner (centralAction g k) := by
  rcases g with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> fin_cases k <;> rfl

theorem ownerAction_corner (g : Transform) (k : Fin 4) :
    ownerAction g (cornerOwner k) = cornerOwner (centralAction g k) := by
  rcases g with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> fin_cases k <;> rfl

/-- Whether increasing the new wall's tangent coordinate decreases the
old wall's tangent coordinate. -/
def wallFlip (g : Transform) (k : Fin 4) : Bool :=
  if g.swap then ![g.reflectX,g.reflectY,g.reflectX,g.reflectY] k
  else ![g.reflectY,g.reflectX,g.reflectY,g.reflectX] k

def branchAction (g : Transform) (b : WallBranch) (k : Fin 4) : Bool :=
  if wallFlip g k then !(b (wallAction g k)) else b (wallAction g k)

def symmetry : Fin 8 → Transform :=
  ![⟨false,false,false⟩,⟨false,false,true⟩,⟨false,true,false⟩,⟨false,true,true⟩,
    ⟨true,false,false⟩,⟨true,false,true⟩,⟨true,true,false⟩,⟨true,true,true⟩]

/-- Clockwise encoding is `(b0,!b1,!b2,b3)`. The representatives have
respectively all equal bits, one exceptional bit, two adjacent bits,
and two opposite bits. Their D4 orbit sizes are 2,8,4,2. -/
def canonicalBranch : Fin 4 → WallBranch :=
  ![![true,false,false,true], ![true,true,true,false],
    ![true,false,true,false], ![true,true,false,false]]

end N12Compact.C1092WallSymmetry
