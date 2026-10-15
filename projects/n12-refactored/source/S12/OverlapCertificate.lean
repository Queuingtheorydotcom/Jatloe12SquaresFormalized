import S12.ConvexOverlap

namespace S12
open S12Pilot

structure ReferenceSquare where
  c : ℚ
  s : ℚ
  side : ℚ
  deriving DecidableEq

def ReferenceSquare.Check (q : ReferenceSquare) : Prop := q.c^2+q.s^2=1 ∧ 0<q.side
instance ReferenceSquare.decidableCheck (q : ReferenceSquare) : Decidable q.Check := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def ReferenceSquare.toSquare (q : ReferenceSquare) (hq : q.Check) : OpenSquare where
  c := q.c
  s := q.s
  loU := -(q.side:ℝ)/2
  loV := -(q.side:ℝ)/2
  side := q.side
  unit_normal := by exact_mod_cast hq.1
  side_pos := by exact_mod_cast hq.2

def ratPoint (p : ℚ × ℚ) : ℝ × ℝ := (p.1,p.2)

def ReferenceSquare.InsideAt (q : ReferenceSquare) (A P : ℚ × ℚ) : Prop :=
  -q.side/2<q.c*(P.1-A.1)+q.s*(P.2-A.2) ∧
  q.c*(P.1-A.1)+q.s*(P.2-A.2)<q.side/2 ∧
  -q.side/2< -q.s*(P.1-A.1)+q.c*(P.2-A.2) ∧
  -q.s*(P.1-A.1)+q.c*(P.2-A.2)<q.side/2
instance ReferenceSquare.decidableInsideAt (q : ReferenceSquare) (A P : ℚ × ℚ) : Decidable (q.InsideAt A P) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem ReferenceSquare.insideAt_sound (q : ReferenceSquare) (hq : q.Check) (A P : ℚ × ℚ)
    (hi : q.InsideAt A P) : ratPoint P-ratPoint A∈squareSet (q.toSquare hq) := by
  have hh :
      -(q.side:ℝ)/2<(q.c:ℝ)*((P.1:ℝ)-A.1)+(q.s:ℝ)*((P.2:ℝ)-A.2) ∧
      (q.c:ℝ)*((P.1:ℝ)-A.1)+(q.s:ℝ)*((P.2:ℝ)-A.2)<(q.side:ℝ)/2 ∧
      -(q.side:ℝ)/2< -(q.s:ℝ)*((P.1:ℝ)-A.1)+(q.c:ℝ)*((P.2:ℝ)-A.2) ∧
      -(q.s:ℝ)*((P.1:ℝ)-A.1)+(q.c:ℝ)*((P.2:ℝ)-A.2)<(q.side:ℝ)/2 := by exact_mod_cast hi
  change (q.toSquare hq).Inside _ _
  dsimp [ReferenceSquare.toSquare,OpenSquare.Inside,InBands,ratPoint]
  exact ⟨hh.1,by linarith [hh.2.1],hh.2.2.1,by linarith [hh.2.2.2]⟩

structure VertexWitness where
  centerA : ℚ × ℚ
  centerB : ℚ × ℚ
  point : ℚ × ℚ
  deriving DecidableEq

structure OverlapCertificate where
  first : {q : ReferenceSquare // q.Check}
  second : {q : ReferenceSquare // q.Check}
  verticesA : List (ℚ × ℚ)
  verticesB : List (ℚ × ℚ)
  witnesses : List VertexWitness

def OverlapCertificate.Check (w : OverlapCertificate) : Prop :=
  ∀ A∈w.verticesA,∀ B∈w.verticesB,∃ v∈w.witnesses,
    v.centerA=A ∧ v.centerB=B ∧ w.first.val.InsideAt A v.point ∧ w.second.val.InsideAt B v.point
instance OverlapCertificate.decidableCheck (w : OverlapCertificate) : Decidable w.Check := inferInstanceAs (Decidable (∀ A∈_,_))

noncomputable def vertexHull (V : List (ℚ × ℚ)) : Set (ℝ × ℝ) :=
  convexHull ℝ (ratPoint '' {v | v∈V})

theorem OverlapCertificate.sound (w : OverlapCertificate) (hw : w.Check)
    (A B : ℝ × ℝ) (hA : A∈vertexHull w.verticesA) (hB : B∈vertexHull w.verticesB) :
    OverlapsAt (w.first.val.toSquare w.first.property) (w.second.val.toSquare w.second.property) A B := by
  apply vertex_overlap_extends _ _ _ _ _ A hA B hB
  intro A hA B hB
  obtain ⟨a,ha,rfl⟩ := hA
  obtain ⟨b,hb,rfl⟩ := hB
  obtain ⟨v,_,_,_,h0,h1⟩ := hw a ha b hb
  exact ⟨ratPoint v.point,w.first.val.insideAt_sound w.first.property a v.point h0,
    w.second.val.insideAt_sound w.second.property b v.point h1⟩

/-- An overlap certificate excludes two actual squares once their enclosed
centers and certified inner reference squares are supplied. -/
theorem OverlapCertificate.excludes (w : OverlapCertificate) (hw : w.Check)
    (q r : OpenSquare) (A B : ℝ × ℝ)
    (hA : A∈vertexHull w.verticesA) (hB : B∈vertexHull w.verticesB)
    (hq : ∀ P : ℝ × ℝ,P-A∈squareSet (w.first.val.toSquare w.first.property) → P∈squareSet q)
    (hr : ∀ P : ℝ × ℝ,P-B∈squareSet (w.second.val.toSquare w.second.property) → P∈squareSet r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : False := by
  obtain ⟨P,h0,h1⟩ := w.sound hw A B hA hB
  exact hd P.1 P.2 ⟨hq P h0,hr P h1⟩

#print axioms OverlapCertificate.excludes
end S12
