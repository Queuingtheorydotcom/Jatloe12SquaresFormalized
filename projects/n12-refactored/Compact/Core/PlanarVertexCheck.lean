import Compact.Core.PlanarVertex
import Mathlib.Data.List.Dedup

/-!
An exact integer checker for the complete boundary-intersection criterion.
No vertices, rational divisions, cells or subdivision histories are stored.
The determinant sign clears the common denominator positively; open forbidden
faces remain strictly positive and their equality boundaries stay feasible.
-/

set_option Elab.async false

namespace N12Compact.PlanarVertexCheck

open IntegerSupport PlanarVertex

structure Vertex where
  x : Int
  y : Int
  denominator : Int
  deriving DecidableEq

def sign (a b : Row) : Int := if 0 ≤ det a b then 1 else -1

def vertex (a b : Row) : Vertex :=
  ⟨sign a b * (a.y * b.constant - a.constant * b.y),
    sign a b * (a.constant * b.x - a.x * b.constant),
    sign a b * det a b⟩

def Vertex.eval (v : Vertex) (row : Row) : Int :=
  row.x * v.x + row.y * v.y + row.constant * v.denominator

theorem denominator_positive (a b : Row) (h : det a b ≠ 0) :
    0 < (vertex a b).denominator := by
  dsimp [vertex, sign]
  split_ifs <;> simp only [one_mul, neg_one_mul] <;> omega

/-- A polynomial identity relates the integer numerator to any actual
intersection point; uniqueness or rational computation is not assumed. -/
theorem eval_identity (a b row : Row) (p : Point)
    (ha : a.eval p = 0) (hb : b.eval p = 0) :
    ((vertex a b).eval row : ℝ) =
      ((vertex a b).denominator : ℝ) * row.eval p := by
  have hx : (det a b : ℝ) * p 0 =
      (a.y : ℝ) * b.constant - (a.constant : ℝ) * b.y := by
    calc
      _ = (b.y : ℝ) * a.eval p - (a.y : ℝ) * b.eval p +
          ((a.y : ℝ) * b.constant - (a.constant : ℝ) * b.y) := by
            simp only [det, Row.eval, Int.cast_sub, Int.cast_mul]
            ring
      _ = _ := by rw [ha, hb]; ring
  have hy : (det a b : ℝ) * p 1 =
      (a.constant : ℝ) * b.x - (a.x : ℝ) * b.constant := by
    calc
      _ = (a.x : ℝ) * b.eval p - (b.x : ℝ) * a.eval p +
          ((a.constant : ℝ) * b.x - (a.x : ℝ) * b.constant) := by
            simp only [det, Row.eval, Int.cast_sub, Int.cast_mul]
            ring
      _ = _ := by rw [ha, hb]; ring
  simp only [Vertex.eval, vertex, Int.cast_add, Int.cast_mul, Int.cast_sub]
  rw [← hx, ← hy]
  dsimp [Row.eval]
  ring

theorem nonnegative_iff (a b row : Row) (p : Point) (hd : det a b ≠ 0)
    (ha : a.eval p = 0) (hb : b.eval p = 0) :
    0 ≤ (vertex a b).eval row ↔ 0 ≤ row.eval p := by
  have hden : (0 : ℝ) < (vertex a b).denominator := by
    exact_mod_cast denominator_positive a b hd
  have he := eval_identity a b row p ha hb
  constructor
  · intro h
    have h' : (0 : ℝ) ≤ (vertex a b).eval row := by exact_mod_cast h
    nlinarith only [hden, he, h']
  · intro h
    have h' := mul_nonneg hden.le h
    rw [← he] at h'
    exact_mod_cast h'

theorem positive_iff (a b row : Row) (p : Point) (hd : det a b ≠ 0)
    (ha : a.eval p = 0) (hb : b.eval p = 0) :
    0 < (vertex a b).eval row ↔ 0 < row.eval p := by
  have hden : (0 : ℝ) < (vertex a b).denominator := by
    exact_mod_cast denominator_positive a b hd
  have he := eval_identity a b row p ha hb
  constructor
  · intro h
    have h' : (0 : ℝ) < (vertex a b).eval row := by exact_mod_cast h
    nlinarith only [hden, he, h']
  · intro h
    have h' := mul_pos hden h
    rw [← he] at h'
    exact_mod_cast h'

def Vertex.Feasible (v : Vertex) (base : List Row) (forbidden : List (List Row)) : Prop :=
  (∀ row ∈ base, 0 ≤ v.eval row) ∧
    ∀ block ∈ forbidden, ¬(∀ row ∈ block, 0 < v.eval row)

instance (v : Vertex) (base : List Row) (forbidden : List (List Row)) :
    Decidable (v.Feasible base forbidden) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem feasible_iff (a b : Row) (base : List Row) (forbidden : List (List Row))
    (p : Point) (hd : det a b ≠ 0) (ha : a.eval p = 0) (hb : b.eval p = 0) :
    (vertex a b).Feasible base forbidden ↔ PlanarVertex.Feasible base forbidden p := by
  constructor
  · rintro ⟨hbase, hforbidden⟩
    refine ⟨fun row hr => (nonnegative_iff a b row p hd ha hb).mp (hbase row hr), ?_⟩
    intro block hblock all
    apply hforbidden block hblock
    intro row hr
    exact (positive_iff a b row p hd ha hb).mpr (all row hr)
  · rintro ⟨hbase, hforbidden⟩
    refine ⟨fun row hr => (nonnegative_iff a b row p hd ha hb).mpr (hbase row hr), ?_⟩
    intro block hblock all
    apply hforbidden block hblock
    intro row hr
    exact (positive_iff a b row p hd ha hb).mp (all row hr)

def PairCheck (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (a b : Row) : Prop :=
  det a b = 0 ∨ ((vertex a b).Feasible base forbidden →
    ∀ target ∈ targets, 0 ≤ (vertex a b).eval target)

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row)
    (a b : Row) : Decidable (PairCheck base forbidden targets a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Every boundary pair is checked, including candidates on open-block
boundaries. No witness list may silently omit an unfavorable intersection. -/
def Check (base : List Row) (forbidden : List (List Row)) (targets : List Row) : Prop :=
  let boundaries := (base ++ forbidden.flatten).dedup
  ∀ a ∈ boundaries, ∀ b ∈ boundaries, PairCheck base forbidden targets a b

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row) :
    Decidable (Check base forbidden targets) :=
  inferInstanceAs (Decidable (∀ a ∈ _, ∀ b ∈ _, _))

theorem Check.vertexBound {base : List Row} {forbidden : List (List Row)} {targets : List Row}
    (checked : Check base forbidden targets) (target : Row) (ht : target ∈ targets) :
    VertexBound base forbidden target := by
  intro a ha b hb hd p hap hbp hp
  have ha' : a ∈ (base ++ forbidden.flatten).dedup := List.mem_dedup.mpr ha
  have hb' : b ∈ (base ++ forbidden.flatten).dedup := List.mem_dedup.mpr hb
  rcases checked a ha' b hb' with hzero | hcheck
  · exact (hd hzero).elim
  · apply (nonnegative_iff a b target p hd hap hbp).mp
    exact hcheck ((feasible_iff a b base forbidden p hd hap hbp).mpr hp) target ht

theorem Check.sound {base : List Row} {forbidden : List (List Row)} {targets : List Row}
    (checked : Check base forbidden targets) (box : BoxNormals base)
    (p : Point) (hp : PlanarVertex.Feasible base forbidden p) :
    ∀ target ∈ targets, 0 ≤ target.eval p := by
  intro target ht
  exact nonnegative_of_vertices base forbidden box target (checked.vertexBound target ht) p hp

#print axioms Check.sound

end N12Compact.PlanarVertexCheck
