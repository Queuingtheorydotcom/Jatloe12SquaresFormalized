import Compact.Bridge.DirectPoseCover
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FinCases

/-! Derive integer input rows from the original geometric formulas.
Only a few input indices are stored per root; compulsory and forbidden
coefficients are computed once from the existing angle and point data.
Least common denominators keep the exact integer tests small. -/

namespace N12Compact.DirectPoseCover

open S12 IntegerSupport PlanarVertex

def Form.commonDenominator (r : LinearConstraint 2) : Nat :=
  ((r.form.coeff 0).den.lcm (r.form.coeff 1).den).lcm r.form.constant.den

theorem Form.commonDenominator_pos (r : LinearConstraint 2) :
    0 < Form.commonDenominator r :=
  Nat.lcm_pos (Nat.lcm_pos (r.form.coeff 0).den_pos (r.form.coeff 1).den_pos)
    r.form.constant.den_pos

private theorem scaled_numerator (q : ℚ) (d : Nat) (hd : q.den ∣ d) :
    ((q.num * (d / q.den : Nat) : Int) : ℚ) = q * d := by
  have he : q.den * (d / q.den) = d := Nat.mul_div_cancel' hd
  have he' : (q.den : ℚ) * (d / q.den : Nat) = d := by exact_mod_cast he
  have hq : (q.num : ℚ) = q * q.den :=
    (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hq, mul_assoc, he']

private theorem normalized_numerator (q : ℚ) (d : Nat) (hp : 0 < d)
    (hd : q.den ∣ d) :
    ((q.num * (d / q.den : Nat) : Int) : ℚ) / d = q := by
  rw [scaled_numerator q d hd]
  exact mul_div_cancel_right₀ q (by exact_mod_cast hp.ne')

/-- Exact, computable integer encoding of any original affine constraint.
The strictness bit is copied verbatim. -/
def Form.encode (r : LinearConstraint 2) : Form :=
  let d := Form.commonDenominator r
  ⟨⟨(r.form.coeff 0).num * (d / (r.form.coeff 0).den : Nat),
     (r.form.coeff 1).num * (d / (r.form.coeff 1).den : Nat),
     r.form.constant.num * (d / r.form.constant.den : Nat), r.strict⟩,
   d - 1⟩

@[simp] theorem Form.encode_strict (r : LinearConstraint 2) :
    (Form.encode r).row.strict = r.strict := rfl

@[simp] theorem Form.decode_encode (r : LinearConstraint 2) :
    (Form.encode r).decode = r := by
  let d := Form.commonDenominator r
  have hd : 0 < d := Form.commonDenominator_pos r
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_of_lt hd)
  have hx : (r.form.coeff 0).den ∣ d :=
    (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _)
  have hy : (r.form.coeff 1).den ∣ d :=
    (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
  have hk : r.form.constant.den ∣ d := Nat.dvd_lcm_right _ _
  have xeq := normalized_numerator (r.form.coeff 0) d hd hx
  have yeq := normalized_numerator (r.form.coeff 1) d hd hy
  have keq := normalized_numerator r.form.constant d hd hk
  have coeffeq :
      (fun i : Fin 2 => if i.val = 0 then
        ((r.form.coeff 0).num * (d / (r.form.coeff 0).den : Nat) : Int) / (d : ℚ)
        else ((r.form.coeff 1).num * (d / (r.form.coeff 1).den : Nat) : Int) / (d : ℚ))
      = r.form.coeff := by
    funext i
    fin_cases i
    · simpa using xeq
    · simpa using yeq
  change LinearConstraint.mk
    (Affine.mk (fun i => if i.val = 0 then
      ((r.form.coeff 0).num * (d / (r.form.coeff 0).den : Nat) : Int) / ((d - 1 + 1 : Nat) : ℚ)
      else ((r.form.coeff 1).num * (d / (r.form.coeff 1).den : Nat) : Int) / ((d - 1 + 1 : Nat) : ℚ))
      (((r.form.constant.num * (d / r.form.constant.den : Nat) : Int) : ℚ) /
        ((d - 1 + 1 : Nat) : ℚ))) r.strict = r
  rw [hpred, coeffeq, keq]

@[simp] theorem decode_encode_list (rows : List (LinearConstraint 2)) :
    (rows.map Form.encode).map Form.decode = rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [List.map_cons, Form.decode_encode, ih]

def selectedForms (rows : List (LinearConstraint 2))
    (indices : List (Fin rows.length)) : List Form :=
  indices.map (fun i => Form.encode (rows.get i))

theorem selectedForms_decode_mem (rows : List (LinearConstraint 2))
    (indices : List (Fin rows.length)) (f : Form)
    (hf : f ∈ selectedForms rows indices) : f.decode ∈ rows := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
  rw [Form.decode_encode]
  exact List.get_mem _ _

/-- The only serialized geometric choices are indices into the original
input list and the desired reduced output. All forbidden blocks retain
their exact original formulas and their open boundaries. -/
def sourceRoot (angle : {w : AngleEnclosure // w.Check})
    (inside outside : List (ℚ × ℚ))
    (indices : List (Fin (poseInputs angle.val inside).length))
    (result : Option (List Form)) : Root where
  angle := angle
  base := selectedForms (poseInputs angle.val inside) indices
  forbidden := (poseForbidden angle.val outside).map (List.map Form.encode)
  result := result

/-- Numeric replay need prove only bounding normals, the finite vertex
check, and target strictness. Membership in the original geometry follows
once for every generated root from exact encoding. -/
theorem sourceRoot_check (angle : {w : AngleEnclosure // w.Check})
    (inside outside : List (ℚ × ℚ))
    (indices : List (Fin (poseInputs angle.val inside).length))
    (result : Option (List Form))
    (box : BoxNormals (sourceRoot angle inside outside indices result).baseRows)
    (numeric : PlanarVertexCheck.Check
      (sourceRoot angle inside outside indices result).baseRows
      (sourceRoot angle inside outside indices result).forbiddenRows
      (sourceRoot angle inside outside indices result).targetRows)
    (strict : (sourceRoot angle inside outside indices result).strictOK) :
    (sourceRoot angle inside outside indices result).Check inside outside := by
  refine ⟨box, numeric, ?_, ?_, strict⟩
  · exact selectedForms_decode_mem (poseInputs angle.val inside) indices
  · intro block hb
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hb
    simpa only [decode_encode_list, sourceRoot] using horiginal

#print axioms Form.decode_encode
#print axioms sourceRoot_check
end N12Compact.DirectPoseCover
