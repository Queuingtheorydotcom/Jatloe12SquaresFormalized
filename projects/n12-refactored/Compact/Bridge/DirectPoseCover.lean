import Compact.Core.PlanarVertexCheck
import S12.OrientedCoverage

/-! Direct reduced-pose coverage from actual compulsory/excluded points.
The continuous angle and original OpenSquare hypotheses are unchanged.
No raw pose forest or independently asserted polygon coverage is needed. -/

namespace N12Compact.DirectPoseCover

open S12 S12Pilot IntegerSupport PlanarVertex

/-- Positive scaling is structural: the stored denominator is one less than
the actual denominator. Integer checking never needs rational division. -/
structure Form where
  row : Row
  denominatorPred : Nat
  deriving DecidableEq

def Form.decode (f : Form) : LinearConstraint 2 :=
  f.row.normalized (f.denominatorPred + 1)

theorem Form.holds_iff (f : Form) (p : Point) :
    f.decode.Holds p ↔ f.row.Holds p :=
  f.row.normalized_holds_iff _ (Nat.succ_pos _) p

def Form.StrictOK (f : Form) : Prop :=
  f.row.strict = false ∨ (f.row.x = 0 ∧ f.row.y = 0 ∧ 0 < f.row.constant)

instance (f : Form) : Decidable f.StrictOK := inferInstanceAs (Decidable (_ ∨ _))

theorem Form.holds_of_nonnegative (f : Form) (ok : f.StrictOK) (p : Point)
    (h : 0 ≤ f.row.eval p) : f.decode.Holds p := by
  apply (f.holds_iff p).mpr
  rcases ok with hs | ⟨hx, hy, hc⟩
  · simpa only [Row.Holds, hs, Bool.false_eq_true, ↓reduceIte] using h
  · have hc' : (0 : ℝ) < f.row.constant := by exact_mod_cast hc
    have he : 0 < f.row.eval p := by simpa only [Row.eval, hx, hy,
      Int.cast_zero, zero_mul, zero_add] using hc'
    cases hs : f.row.strict with
    | false => simpa only [Row.Holds, hs, Bool.false_eq_true, ↓reduceIte] using he.le
    | true => simpa only [Row.Holds, hs, ↓reduceIte] using he

theorem Form.holds_of_positive (f : Form) (p : Point)
    (h : 0 < f.row.eval p) : f.decode.Holds p := by
  apply (f.holds_iff p).mpr
  cases hs : f.row.strict with
  | false => simpa only [Row.Holds, hs, Bool.false_eq_true, ↓reduceIte] using h.le
  | true => simpa only [Row.Holds, hs, ↓reduceIte] using h

structure Root where
  angle : {w : AngleEnclosure // w.Check}
  base : List Form
  forbidden : List (List Form)
  result : Option (List Form)

def Root.baseRows (root : Root) : List Row := root.base.map Form.row
def Root.forbiddenRows (root : Root) : List (List Row) :=
  root.forbidden.map (List.map Form.row)

def Root.targetRows (root : Root) : List Row :=
  match root.result with
  | none => [⟨0, 0, -1, false⟩]
  | some forms => forms.map Form.row

def Root.strictOK (root : Root) : Prop :=
  match root.result with
  | none => True
  | some forms => ∀ f ∈ forms, f.StrictOK

instance (root : Root) : Decidable root.strictOK := by
  unfold Root.strictOK
  cases root.result <;> infer_instance

def Root.Check (root : Root) (inside outside : List (ℚ × ℚ)) : Prop :=
  BoxNormals root.baseRows ∧
  PlanarVertexCheck.Check root.baseRows root.forbiddenRows root.targetRows ∧
  (∀ f ∈ root.base, f.decode ∈ poseInputs root.angle.val inside) ∧
  (∀ block ∈ root.forbidden,
    block.map Form.decode ∈ poseForbidden root.angle.val outside) ∧
  root.strictOK

instance (root : Root) (inside outside : List (ℚ × ℚ)) :
    Decidable (root.Check inside outside) := by
  unfold Root.Check BoxNormals
  infer_instance

/-- Exactly one reduced pose, or an empty angle interval. The latter is
proved by the same checker with the impossible target -1>=0. -/
def Root.leaves (root : Root) : List PoseLeaf :=
  match root.result with
  | none => []
  | some forms => [⟨root.angle, forms.map Form.decode⟩]

theorem Root.sound (root : Root) (inside outside : List (ℚ × ℚ))
    (checked : root.Check inside outside) (q : OpenSquare) (t : ℝ)
    (hc : q.c = normalC t) (hs : q.s = normalS t)
    (ht₀ : (root.angle.val.lower : ℝ) ≤ t) (ht₁ : t ≤ (root.angle.val.upper : ℝ))
    (ha : 1 < q.side) (hsize : q.side ≤ 1001 / 1000) (hbox : InsideContainer q)
    (hi : ∀ P ∈ inside, q.Inside P.1 P.2)
    (ho : ∀ P ∈ outside, ¬q.Inside P.1 P.2) :
    ∃ forms, root.result = some forms ∧
      ∀ f ∈ forms, f.decode.Holds ![centerX q, centerY q] := by
  obtain ⟨box, numeric, inputs, forbidden, strict⟩ := checked
  let p : Point := ![centerX q, centerY q]
  have hinput := poseInputs_sound root.angle.val root.angle.property inside q t
    hc hs ht₀ ht₁ ha hsize hbox hi
  have houtside := poseForbidden_sound root.angle.val root.angle.property outside q t
    hc hs ht₀ ht₁ ha ho
  have feasible : PlanarVertex.Feasible root.baseRows root.forbiddenRows p := by
    constructor
    · intro r hr
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
      exact f.row.nonneg p ((f.holds_iff p).mp (hinput f.decode (inputs f hf)))
    · intro block hb allPositive
      obtain ⟨forms, hforms, rfl⟩ := List.mem_map.mp hb
      apply houtside (forms.map Form.decode) (forbidden forms hforms)
      intro constraint hconstraint
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hconstraint
      exact f.holds_of_positive p (allPositive f.row (List.mem_map.mpr ⟨f, hf, rfl⟩))
  have values := numeric.sound box p feasible
  cases hr : root.result with
  | none =>
      have bad := values ⟨0, 0, -1, false⟩ (by simp [Root.targetRows, hr])
      norm_num [Row.eval] at bad
  | some forms =>
      have strict' : ∀ f ∈ forms, f.StrictOK := by
        simpa only [Root.strictOK, hr] using strict
      refine ⟨forms, rfl, ?_⟩
      intro f hf
      apply f.holds_of_nonnegative (strict' f hf) p
      exact values f.row (by simp only [Root.targetRows, hr]; exact List.mem_map.mpr ⟨f, hf, rfl⟩)

structure Owner where
  inside : List (ℚ × ℚ)
  outside : List (ℚ × ℚ)
  roots : List {root : Root // root.Check inside outside}

def Owner.Check (owner : Owner) : Prop :=
  CoversInterval 0 1 (owner.roots.map (fun root => root.val.angle.val))

instance (owner : Owner) : Decidable owner.Check :=
  inferInstanceAs (Decidable (CoversInterval _ _ _))

def Owner.leaves (owner : Owner) : List PoseLeaf :=
  owner.roots.flatMap (fun root => root.val.leaves)

/-- Complete original owner enclosure, including the exact continuous angle
witness and inner-reference containment required by downstream pruning. -/
theorem Owner.oriented_sound (owner : Owner) (checked : owner.Check) (q : OpenSquare)
    (ha : 1 < q.side) (hsize : q.side ≤ 1001 / 1000) (hbox : InsideContainer q)
    (hi : ∀ P ∈ owner.inside, q.Inside P.1 P.2)
    (ho : ∀ P ∈ owner.outside, ¬q.Inside P.1 P.2) :
    OrientedPoseCovered owner.leaves q := by
  obtain ⟨r, hc, hs, hside, hX, hY, hinside⟩ := exists_positive_frame q
  obtain ⟨t, ht₀, ht₁, hs', hc'⟩ := first_quadrant_rational r.s r.c hs hc
    (by nlinarith [r.unit_normal])
  obtain ⟨angle, hangle, hlo, hhi⟩ := coversInterval_sound _ 0 1 checked t
    (by simpa using ht₀) (by simpa using ht₁)
  obtain ⟨root, hroot, he⟩ := List.mem_map.mp hangle
  subst angle
  have hi' : ∀ P ∈ owner.inside, r.Inside P.1 P.2 :=
    fun P hP => (hinside _ _).mpr (hi P hP)
  have ho' : ∀ P ∈ owner.outside, ¬r.Inside P.1 P.2 :=
    fun P hP hh => ho P hP ((hinside _ _).mp hh)
  obtain ⟨forms, hforms, holds⟩ := root.val.sound owner.inside owner.outside root.property r t
    hc' hs' hlo hhi (by rw [hside]; exact ha) (by rw [hside]; exact hsize)
    (fun x y hh => hbox x y ((hinside x y).mp hh)) hi' ho'
  refine ⟨⟨root.val.angle, forms.map Form.decode⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨root, hroot, ?_⟩
    simp only [Root.leaves, hforms, List.mem_singleton]
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    simpa only [hX, hY] using holds g hg
  · intro P hP
    apply (hinside P.1 P.2).mp
    apply root.val.angle.val.inner_sound root.val.angle.property 1 (by norm_num)
      r t hc' hs' hlo hhi (by norm_num; rw [hside]; exact ha.le) P
    simpa only [hX, hY] using hP
  · exact ⟨r, t, hc', hs', hlo, hhi, hside, hX, hY, hinside⟩

#print axioms Owner.oriented_sound
end N12Compact.DirectPoseCover
