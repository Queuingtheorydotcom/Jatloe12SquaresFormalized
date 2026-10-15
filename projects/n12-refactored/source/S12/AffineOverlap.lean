import S12.LinearImplication
import S12.OverlapCertificate

namespace S12
open S12Pilot
open scoped BigOperators
set_option maxHeartbeats 0

def Affine.const (n : Nat) (a : ℚ) : Affine n := ⟨fun _ => 0,a⟩
def Affine.coord (n : Nat) (i : Fin n) : Affine n := ⟨fun j => if j=i then 1 else 0,0⟩
def Affine.sub {n : Nat} (f g : Affine n) : Affine n := f.add (g.scale (-1))

@[simp] theorem Affine.eval_const (n : Nat) (a : ℚ) (x : Fin n→ℝ) :
    (Affine.const n a).eval x=a := by simp [Affine.const,Affine.eval]
@[simp] theorem Affine.eval_coord (n : Nat) (i : Fin n) (x : Fin n→ℝ) :
    (Affine.coord n i).eval x=x i := by
  simp only [Affine.coord,Affine.eval,add_zero]
  rw [Finset.sum_eq_single i] <;> simp_all
@[simp] theorem Affine.eval_sub {n : Nat} (f g : Affine n) (x : Fin n→ℝ) :
    (f.sub g).eval x=f.eval x-g.eval x := by simp [Affine.sub]; ring

def insideAffineForms {n : Nat} (r : ReferenceSquare) (cx cy px py : Affine n) : List (LinearConstraint n) :=
  let dx := px.sub cx
  let dy := py.sub cy
  let u := (dx.scale r.c).add (dy.scale r.s)
  let v := (dx.scale (-r.s)).add (dy.scale r.c)
  let a := Affine.const n (r.side/2)
  [⟨a.add u,true⟩,⟨a.sub u,true⟩,⟨a.add v,true⟩,⟨a.sub v,true⟩]

theorem insideAffineForms_sound {n : Nat} (r : ReferenceSquare) (hr : r.Check)
    (cx cy px py : Affine n) (x : Fin n→ℝ)
    (hh : ∀ f∈insideAffineForms r cx cy px py,f.Holds x) :
    (px.eval x-cx.eval x,py.eval x-cy.eval x)∈squareSet (r.toSquare hr) := by
  dsimp [insideAffineForms] at hh
  simp only [List.forall_mem_cons,List.forall_mem_nil,and_true] at hh
  obtain ⟨h0,h1,h2,h3⟩ := hh
  simp only [LinearConstraint.Holds,if_true,Affine.eval_add,Affine.eval_sub,Affine.eval_scale,Affine.eval_const] at h0 h1 h2 h3
  change InBands _ _ _ _ _
  dsimp [ReferenceSquare.toSquare]
  push_cast at h0 h1 h2 h3
  dsimp [InBands]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- The exact real meaning of the four affine interior constraints. -/
theorem insideAffineForms_iff {n : Nat} (r : ReferenceSquare)
    (cx cy px py : Affine n) (x : Fin n→ℝ) :
    (∀ f∈insideAffineForms r cx cy px py,f.Holds x) ↔
    |(r.c:ℝ)*(px.eval x-cx.eval x)+(r.s:ℝ)*(py.eval x-cy.eval x)|<(r.side:ℝ)/2 ∧
    |-(r.s:ℝ)*(px.eval x-cx.eval x)+(r.c:ℝ)*(py.eval x-cy.eval x)|<(r.side:ℝ)/2 := by
  simp only [insideAffineForms,List.forall_mem_cons,List.forall_mem_nil,and_true,
    LinearConstraint.Holds,if_true,Affine.eval_add,Affine.eval_sub,Affine.eval_scale,Affine.eval_const]
  simp only [List.mem_nil_iff,false_implies,implies_true,and_true]
  push_cast
  rw [abs_lt,abs_lt]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨⟨by nlinarith only [h0,h1,h2,h3],by nlinarith only [h0,h1,h2,h3]⟩,⟨by nlinarith only [h0,h1,h2,h3],by nlinarith only [h0,h1,h2,h3]⟩⟩
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    refine ⟨?_,?_,?_,?_⟩
    all_goals nlinarith only [h0,h1,h2,h3]

def Affine.liftLeft (f : Affine 2) : Affine 4 :=
  ⟨fun i => if h : i.val<2 then f.coeff ⟨i.val,h⟩ else 0,f.constant⟩
def Affine.liftRight (f : Affine 2) : Affine 4 :=
  ⟨fun i => if h : 2≤i.val then f.coeff ⟨i.val-2,by omega⟩ else 0,f.constant⟩
def LinearConstraint.liftLeft (f : LinearConstraint 2) : LinearConstraint 4 := ⟨f.form.liftLeft,f.strict⟩
def LinearConstraint.liftRight (f : LinearConstraint 2) : LinearConstraint 4 := ⟨f.form.liftRight,f.strict⟩

theorem Affine.eval_liftLeft (f : Affine 2) (x : Fin 4→ℝ) :
    f.liftLeft.eval x=f.eval ![x 0,x 1] := by
  simp [Affine.liftLeft,Affine.eval,Fin.sum_univ_succ]
theorem Affine.eval_liftRight (f : Affine 2) (x : Fin 4→ℝ) :
    f.liftRight.eval x=f.eval ![x 2,x 3] := by
  simp [Affine.liftRight,Affine.eval,Fin.sum_univ_succ]

theorem LinearConstraint.holds_liftLeft (f : LinearConstraint 2) (x : Fin 4→ℝ) :
    f.liftLeft.Holds x ↔ f.Holds ![x 0,x 1] := by
  simp only [LinearConstraint.Holds,LinearConstraint.liftLeft,Affine.eval_liftLeft]
theorem LinearConstraint.holds_liftRight (f : LinearConstraint 2) (x : Fin 4→ℝ) :
    f.liftRight.Holds x ↔ f.Holds ![x 2,x 3] := by
  simp only [LinearConstraint.Holds,LinearConstraint.liftRight,Affine.eval_liftRight]

structure AffineOverlapCertificate where
  first : {r : ReferenceSquare // r.Check}
  second : {r : ReferenceSquare // r.Check}
  inputsA : List (LinearConstraint 2)
  inputsB : List (LinearConstraint 2)
  pointX : Affine 4
  pointY : Affine 4
  proofs : List (List (ℚ × LinearConstraint 4))

def AffineOverlapCertificate.inputs (w : AffineOverlapCertificate) : List (LinearConstraint 4) :=
  w.inputsA.map LinearConstraint.liftLeft++w.inputsB.map LinearConstraint.liftRight

def AffineOverlapCertificate.targets (w : AffineOverlapCertificate) : List (LinearConstraint 4) :=
  insideAffineForms w.first.val (Affine.coord 4 0) (Affine.coord 4 1) w.pointX w.pointY++
  insideAffineForms w.second.val (Affine.coord 4 2) (Affine.coord 4 3) w.pointX w.pointY

def AffineOverlapCertificate.Check (w : AffineOverlapCertificate) : Prop :=
  ∀ target∈w.targets,∃ terms∈w.proofs,LinearImplicationCheck w.inputs target terms
instance AffineOverlapCertificate.decidableCheck (w : AffineOverlapCertificate) : Decidable w.Check :=
  inferInstanceAs (Decidable (∀ target∈w.targets,_))

/-- A checked affine witness proves overlap from halfplane constraints
alone. No correctness of a polygon vertex algorithm is assumed. -/
theorem AffineOverlapCertificate.sound (w : AffineOverlapCertificate) (hw : w.Check)
    (x : Fin 4→ℝ) (hA : ∀ f∈w.inputsA,f.Holds ![x 0,x 1])
    (hB : ∀ f∈w.inputsB,f.Holds ![x 2,x 3]) :
    OverlapsAt (w.first.val.toSquare w.first.property) (w.second.val.toSquare w.second.property)
      (x 0,x 1) (x 2,x 3) := by
  have hin : ∀ f∈w.inputs,f.Holds x := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
      exact (LinearConstraint.holds_liftLeft r x).mpr (hA r hr)
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
      exact (LinearConstraint.holds_liftRight r x).mpr (hB r hr)
  have hout : ∀ f∈w.targets,f.Holds x := by
    intro f hf
    obtain ⟨terms,_,ht⟩ := hw f hf
    exact linear_implication_sound _ f terms ht x hin
  refine ⟨(w.pointX.eval x,w.pointY.eval x),?_,?_⟩
  · have hh := insideAffineForms_sound w.first.val w.first.property (Affine.coord 4 0) (Affine.coord 4 1)
      w.pointX w.pointY x (fun f hf => hout f (List.mem_append_left _ hf))
    simpa only [Affine.eval_coord] using hh
  · have hh := insideAffineForms_sound w.second.val w.second.property (Affine.coord 4 2) (Affine.coord 4 3)
      w.pointX w.pointY x (fun f hf => hout f (List.mem_append_right _ hf))
    simpa only [Affine.eval_coord] using hh

#print axioms AffineOverlapCertificate.sound
end S12
