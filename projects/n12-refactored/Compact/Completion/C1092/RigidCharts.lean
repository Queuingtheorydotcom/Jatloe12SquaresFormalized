import Compact.Geometry.ClosedFrames

/-! Literal rigid coordinate charts, preserving the common side. The signed
transpose keeps a canonical cosine and exchanges the same physical faces. -/
namespace N12Compact.C1092RigidCharts
open S12 S12Pilot
set_option Elab.async false

def translate (Q : OpenSquare) (x y : ℝ) : OpenSquare where
  c := Q.c
  s := Q.s
  loU := Q.loU-Q.c*x-Q.s*y
  loV := Q.loV+Q.s*x-Q.c*y
  side := Q.side
  unit_normal := Q.unit_normal
  side_pos := Q.side_pos

def opposite (Q : OpenSquare) : OpenSquare where
  c := Q.c
  s := Q.s
  loU := -Q.loU-Q.side
  loV := -Q.loV-Q.side
  side := Q.side
  unit_normal := Q.unit_normal
  side_pos := Q.side_pos

def swap (Q : OpenSquare) : OpenSquare where
  c := Q.c
  s := -Q.s
  loU := Q.loV
  loV := Q.loU
  side := Q.side
  unit_normal := by nlinarith only [Q.unit_normal]
  side_pos := Q.side_pos

theorem inside_translate (Q : OpenSquare) (x0 y0 x y : ℝ) :
    (translate Q x0 y0).Inside x y ↔ Q.Inside (x+x0) (y+y0) := by
  dsimp [translate,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3]

theorem inside_opposite (Q : OpenSquare) (x y : ℝ) :
    (opposite Q).Inside x y ↔ Q.Inside (-x) (-y) := by
  dsimp [opposite,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3]

theorem inside_swap (Q : OpenSquare) (x y : ℝ) :
    (swap Q).Inside x y ↔ Q.Inside y x := by
  dsimp [swap,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [h0,h1,h2,h3]

end N12Compact.C1092RigidCharts
