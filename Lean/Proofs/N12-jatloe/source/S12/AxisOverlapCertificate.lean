import S12.SquareAxes
import S12.AffineOverlap
namespace S12
open S12Pilot
set_option maxHeartbeats 0

def ReferenceSquare.ratRadius (r : ReferenceSquare) (nx ny : ℚ) : ℚ :=
  r.side/2*(|nx*r.c+ny*r.s|+|-nx*r.s+ny*r.c|)

noncomputable def ReferenceSquare.atCenter (r : ReferenceSquare) (hr : r.Check) (x y : ℝ) : OpenSquare :=
  (r.toSquare hr).translated (-x) (-y)

theorem ReferenceSquare.atCenter_inside (r : ReferenceSquare) (hr : r.Check) (x y px py : ℝ) :
    (r.atCenter hr x y).Inside px py ↔ (r.toSquare hr).Inside (px-x) (py-y) := by
  rw [ReferenceSquare.atCenter,inside_translated_iff]
  congr 1 <;> ring

theorem ReferenceSquare.atCenter_X (r : ReferenceSquare) (hr : r.Check) (x y : ℝ) :
    centerX (r.atCenter hr x y)=x := by
  have hu : (r.c:ℝ)^2+(r.s:ℝ)^2=1 := (r.toSquare hr).unit_normal
  dsimp [ReferenceSquare.atCenter,ReferenceSquare.toSquare,OpenSquare.translated,centerX]
  linear_combination x*hu

theorem ReferenceSquare.atCenter_Y (r : ReferenceSquare) (hr : r.Check) (x y : ℝ) :
    centerY (r.atCenter hr x y)=y := by
  have hu : (r.c:ℝ)^2+(r.s:ℝ)^2=1 := (r.toSquare hr).unit_normal
  dsimp [ReferenceSquare.atCenter,ReferenceSquare.toSquare,OpenSquare.translated,centerY]
  linear_combination y*hu

theorem ReferenceSquare.ratRadius_sound (r : ReferenceSquare) (hr : r.Check) (x y : ℝ) (nx ny : ℚ) :
    squareRadius (r.atCenter hr x y) nx ny=(r.ratRadius nx ny:ℝ) := by
  simp only [squareRadius,ReferenceSquare.atCenter,OpenSquare.translated,ReferenceSquare.toSquare,
    ReferenceSquare.ratRadius]
  push_cast
  rfl

def pairAxes (a b : ReferenceSquare) : List (ℚ × ℚ) :=
  [(a.c,a.s),(-a.s,a.c),(b.c,b.s),(-b.s,b.c)]

def axisGapForm (a b : ReferenceSquare) (nx ny : ℚ) : LinearConstraint 4 :=
  ⟨⟨![nx,ny,-nx,-ny],a.ratRadius nx ny+b.ratRadius nx ny⟩,true⟩

theorem axisGapForm_holds (a b : ReferenceSquare) (nx ny : ℚ) (x : Fin 4→ℝ) :
    (axisGapForm a b nx ny).Holds x ↔
      (nx:ℝ)*(x 2-x 0)+(ny:ℝ)*(x 3-x 1)<(a.ratRadius nx ny+b.ratRadius nx ny:ℚ) := by
  simp [axisGapForm,LinearConstraint.Holds,Affine.eval,Fin.sum_univ_succ]
  constructor <;> intro h <;> linarith

def axisOverlapForms (a b : ReferenceSquare) : List (LinearConstraint 4) :=
  (pairAxes a b).flatMap (fun n => [axisGapForm a b n.1 n.2,axisGapForm a b (-n.1) (-n.2)])

theorem ratRadius_neg (a : ReferenceSquare) (nx ny : ℚ) :
    a.ratRadius (-nx) (-ny)=a.ratRadius nx ny := by
  unfold ReferenceSquare.ratRadius
  rw [show (-nx)*a.c+(-ny)*a.s=-(nx*a.c+ny*a.s) by ring,
    show -(-nx)*a.s+(-ny)*a.c=-(-nx*a.s+ny*a.c) by ring,abs_neg,abs_neg]

theorem axisOverlapForms_sound (a b : ReferenceSquare) (ha : a.Check) (hb : b.Check)
    (x : Fin 4→ℝ) (h : ∀ f∈axisOverlapForms a b,f.Holds x) :
    OverlapsAt (a.toSquare ha) (b.toSquare hb) (x 0,x 1) (x 2,x 3) := by
  have noAxis : ∀ n∈pairAxes a b,
      ¬AxisSeparates (a.atCenter ha (x 0) (x 1)) (b.atCenter hb (x 2) (x 3)) n.1 n.2 := by
    intro n hn hs
    have hf := h (axisGapForm a b n.1 n.2) (List.mem_flatMap.mpr ⟨n,hn,by simp⟩)
    have hg := h (axisGapForm a b (-n.1) (-n.2)) (List.mem_flatMap.mpr ⟨n,hn,by simp⟩)
    rw [axisGapForm_holds] at hf hg
    rw [ratRadius_neg,ratRadius_neg] at hg
    simp only [AxisSeparates,ReferenceSquare.ratRadius_sound,ReferenceSquare.atCenter_X,ReferenceSquare.atCenter_Y] at hs
    have hstrict : |(n.1:ℝ)*(x 2-x 0)+(n.2:ℝ)*(x 3-x 1)|<
        (a.ratRadius n.1 n.2:ℝ)+(b.ratRadius n.1 n.2:ℝ) := by
      rw [abs_lt]
      push_cast at hf hg
      constructor <;> linarith
    exact (not_lt_of_ge hs) hstrict
  by_cases hov : OverlapsAt (a.toSquare ha) (b.toSquare hb) (x 0,x 1) (x 2,x 3)
  · exact hov
  exfalso
  have hd : ∀ px py,¬((a.atCenter ha (x 0) (x 1)).Inside px py ∧
      (b.atCenter hb (x 2) (x 3)).Inside px py) := by
    intro px py hh
    apply hov
    exact ⟨(px,py),(a.atCenter_inside ha _ _ _ _).mp hh.1,(b.atCenter_inside hb _ _ _ _).mp hh.2⟩
  have hs := square_separating_axes _ _ hd
  rcases hs with hs|hs|hs|hs
  · exact noAxis (a.c,a.s) (by simp [pairAxes]) hs
  · exact noAxis (-a.s,a.c) (by simp [pairAxes]) (by simpa only [ReferenceSquare.atCenter,ReferenceSquare.toSquare,OpenSquare.translated,Prod.fst,Prod.snd,Rat.cast_neg] using hs)
  · exact noAxis (b.c,b.s) (by simp [pairAxes]) hs
  · exact noAxis (-b.s,b.c) (by simp [pairAxes]) (by simpa only [ReferenceSquare.atCenter,ReferenceSquare.toSquare,OpenSquare.translated,Prod.fst,Prod.snd,Rat.cast_neg] using hs)

structure AxisOverlapCertificate where
  first : {r : ReferenceSquare // r.Check}
  second : {r : ReferenceSquare // r.Check}
  inputsA : List (LinearConstraint 2)
  inputsB : List (LinearConstraint 2)
  proofs : List (List (ℚ × LinearConstraint 4))

def AxisOverlapCertificate.inputs (w : AxisOverlapCertificate) : List (LinearConstraint 4) :=
  w.inputsA.map LinearConstraint.liftLeft++w.inputsB.map LinearConstraint.liftRight

def AxisOverlapCertificate.Check (w : AxisOverlapCertificate) : Prop :=
  ∀ target∈axisOverlapForms w.first.val w.second.val,
    ∃ terms∈w.proofs,LinearImplicationCheck w.inputs target terms
instance AxisOverlapCertificate.decidableCheck (w : AxisOverlapCertificate) : Decidable w.Check :=
  inferInstanceAs (Decidable (∀ target∈_,_))

/-- Rational halfplane certificates can prove overlap using the formally proved
separating-axis theorem, without trusting a polygon or LP implementation. -/
theorem AxisOverlapCertificate.sound (w : AxisOverlapCertificate) (hw : w.Check)
    (x : Fin 4→ℝ) (hA : ∀ f∈w.inputsA,f.Holds ![x 0,x 1])
    (hB : ∀ f∈w.inputsB,f.Holds ![x 2,x 3]) :
    OverlapsAt (w.first.val.toSquare w.first.property) (w.second.val.toSquare w.second.property)
      (x 0,x 1) (x 2,x 3) := by
  have hin : ∀ f∈w.inputs,f.Holds x := by
    intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
      exact (LinearConstraint.holds_liftLeft r x).mpr (hA r hr)
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
      exact (LinearConstraint.holds_liftRight r x).mpr (hB r hr)
  apply axisOverlapForms_sound _ _ _ _ x
  intro f hf
  obtain ⟨terms,_,ht⟩ := hw f hf
  exact linear_implication_sound w.inputs f terms ht x hin

#print axioms AxisOverlapCertificate.sound
end S12
