import Compact.Core.IntegerSupport
import Mathlib.Data.Finset.Max

/-! A planar region minus finitely many open convex blocks needs no recorded
cut tree. At a feasible point choose the closed exterior faces it satisfies.
The resulting bounded polygon contains the point and avoids every open block.
Two exact line walks find a vertex with no greater value of a given affine
form. All such vertices use original boundary lines. -/

namespace N12Compact.PlanarVertex

open IntegerSupport

abbrev Point := Fin 2 → ℝ

def _root_.N12Compact.IntegerSupport.Row.slope (r : Row) (d : Point) : ℝ :=
  (r.x : ℝ) * d 0 + (r.y : ℝ) * d 1

def advance (p d : Point) (t : ℝ) : Point := fun i => p i + t * d i

theorem eval_advance (r : Row) (p d : Point) (t : ℝ) :
    r.eval (advance p d t) = r.eval p + t * r.slope d := by
  unfold Row.eval advance Row.slope
  ring

def negate (r : Row) : Row := ⟨-r.x, -r.y, -r.constant, false⟩

@[simp] theorem eval_negate (r : Row) (p : Point) :
    (negate r).eval p = -r.eval p := by
  simp only [Row.eval, negate, Int.cast_neg]
  ring

def det (a b : Row) : ℤ := a.x * b.y - a.y * b.x

@[simp] theorem det_negate_left (a b : Row) : det (negate a) b = -det a b := by
  unfold det negate
  ring

@[simp] theorem det_negate_right (a b : Row) : det a (negate b) = -det a b := by
  unfold det negate
  ring

/-- Actual coordinate wall normals suffice; their positive scales and
constant terms may differ. No externally asserted boundedness is needed. -/
def BoxNormals (rows : List Row) : Prop :=
  (∃ r ∈ rows, 0 < r.x ∧ r.y = 0) ∧
  (∃ r ∈ rows, r.x < 0 ∧ r.y = 0) ∧
  (∃ r ∈ rows, r.x = 0 ∧ 0 < r.y) ∧
  (∃ r ∈ rows, r.x = 0 ∧ r.y < 0)

theorem BoxNormals.mono {a b : List Row} (h : BoxNormals a)
    (hab : ∀ r ∈ a, r ∈ b) : BoxNormals b := by
  rcases h with ⟨⟨r₀, hr₀, h₀⟩, ⟨r₁, hr₁, h₁⟩,
    ⟨r₂, hr₂, h₂⟩, ⟨r₃, hr₃, h₃⟩⟩
  exact ⟨⟨r₀, hab _ hr₀, h₀⟩, ⟨r₁, hab _ hr₁, h₁⟩,
    ⟨r₂, hab _ hr₂, h₂⟩, ⟨r₃, hab _ hr₃, h₃⟩⟩

private theorem negative_slope (rows : List Row) (box : BoxNormals rows)
    (d : Point) (hd : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    ∃ r ∈ rows, r.slope d < 0 := by
  rcases box with ⟨⟨r₀, hr₀, hx₀, hy₀⟩, ⟨r₁, hr₁, hx₁, hy₁⟩,
    ⟨r₂, hr₂, hx₂, hy₂⟩, ⟨r₃, hr₃, hx₃, hy₃⟩⟩
  rcases hd with hd | hd
  · rcases lt_or_gt_of_ne hd with hneg | hpos
    · refine ⟨r₀, hr₀, ?_⟩
      have hx : (0 : ℝ) < r₀.x := by exact_mod_cast hx₀
      simpa only [Row.slope, hy₀, Int.cast_zero, zero_mul, add_zero]
        using mul_neg_of_pos_of_neg hx hneg
    · refine ⟨r₁, hr₁, ?_⟩
      have hx : (r₁.x : ℝ) < 0 := by exact_mod_cast hx₁
      simpa only [Row.slope, hy₁, Int.cast_zero, zero_mul, add_zero]
        using mul_neg_of_neg_of_pos hx hpos
  · rcases lt_or_gt_of_ne hd with hneg | hpos
    · refine ⟨r₂, hr₂, ?_⟩
      have hy : (0 : ℝ) < r₂.y := by exact_mod_cast hy₂
      simpa only [Row.slope, hx₂, Int.cast_zero, zero_mul, zero_add]
        using mul_neg_of_pos_of_neg hy hneg
    · refine ⟨r₃, hr₃, ?_⟩
      have hy : (r₃.y : ℝ) < 0 := by exact_mod_cast hy₃
      simpa only [Row.slope, hx₃, Int.cast_zero, zero_mul, zero_add]
        using mul_neg_of_neg_of_pos hy hpos

/-- Exact first exit along a nonzero direction. The finite minimum concerns
real exit times only in this generic proof, never serialized numeric data. -/
private theorem first_exit (rows : List Row) (box : BoxNormals rows)
    (p d : Point) (hp : ∀ r ∈ rows, 0 ≤ r.eval p)
    (hd : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ r ∈ rows, r.slope d < 0 ∧
      r.eval (advance p d t) = 0 ∧
      ∀ s ∈ rows, 0 ≤ s.eval (advance p d t) := by
  classical
  let active := rows.toFinset.filter (fun r => r.slope d < 0)
  have ha : active.Nonempty := by
    obtain ⟨r, hr, hrd⟩ := negative_slope rows box d hd
    exact ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrd⟩⟩
  obtain ⟨r, hr, hmin⟩ := active.exists_min_image
    (fun r => r.eval p / (-r.slope d)) ha
  have hr' := Finset.mem_filter.mp hr
  have hmem : r ∈ rows := List.mem_toFinset.mp hr'.1
  have hneg : r.slope d < 0 := hr'.2
  let t := r.eval p / (-r.slope d)
  have ht : 0 ≤ t := div_nonneg (hp r hmem) (by linarith)
  refine ⟨t, ht, r, hmem, hneg, ?_, ?_⟩
  · rw [eval_advance]
    have he : t * (-r.slope d) = r.eval p :=
      div_mul_cancel₀ _ (ne_of_gt (by linarith : 0 < -r.slope d))
    nlinarith only [he]
  · intro s hs
    rw [eval_advance]
    by_cases hsd : s.slope d < 0
    · have hsmem : s ∈ active :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, hsd⟩
      have hbound : t * (-s.slope d) ≤ s.eval p :=
        (le_div_iff₀ (by linarith : 0 < -s.slope d)).mp (hmin s hsmem)
      nlinarith only [hbound]
    · have hprod := mul_nonneg ht (le_of_not_gt hsd)
      linarith only [hp s hs, hprod]

/-- Every point of a bounded closed polygon admits a vertex whose value of
the target affine form is no greater. This includes segments and singletons;
the second exit time is allowed to be zero. -/
theorem vertex_below (rows : List Row) (box : BoxNormals rows)
    (target : Row) (p : Point) (hp : ∀ r ∈ rows, 0 ≤ r.eval p) :
    ∃ a ∈ rows, ∃ b ∈ rows, ∃ q : Point,
      det a b ≠ 0 ∧ a.eval q = 0 ∧ b.eval q = 0 ∧
      (∀ r ∈ rows, 0 ≤ r.eval q) ∧ target.eval q ≤ target.eval p := by
  classical
  let d₀ : Point := if 0 ≤ target.x then ![-1, 0] else ![1, 0]
  have hd₀ : d₀ 0 ≠ 0 ∨ d₀ 1 ≠ 0 := by
    left
    dsimp [d₀]
    split_ifs <;> norm_num
  have hf₀ : target.slope d₀ ≤ 0 := by
    dsimp [d₀, Row.slope]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ target.x := by exact_mod_cast h
      simpa using neg_nonpos.mpr h'
    · have h' : (target.x : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h)
      simpa using h'.le
  obtain ⟨t₀, ht₀, a, ha, had, ha0, hp₁⟩ := first_exit rows box p d₀ hp hd₀
  let p₁ := advance p d₀ t₀
  have hfirst : target.eval p₁ ≤ target.eval p := by
    dsimp [p₁]
    rw [eval_advance]
    have hm := mul_nonpos_of_nonneg_of_nonpos ht₀ hf₀
    linarith only [hm]
  let tangent : Point := ![-(a.y : ℝ), (a.x : ℝ)]
  let d₁ : Point := if target.slope tangent ≤ 0 then tangent else fun i => -tangent i
  have hanormal : a.x ≠ 0 ∨ a.y ≠ 0 := by
    by_cases hx : a.x = 0
    · right
      intro hy
      simp [Row.slope, hx, hy] at had
    · exact Or.inl hx
  have hd₁ : d₁ 0 ≠ 0 ∨ d₁ 1 ≠ 0 := by
    rcases hanormal with hx | hy
    · right
      have hx' : (a.x : ℝ) ≠ 0 := by exact_mod_cast hx
      dsimp [d₁, tangent]
      split_ifs <;> simpa using hx'
    · left
      have hy' : (a.y : ℝ) ≠ 0 := by exact_mod_cast hy
      dsimp [d₁, tangent]
      split_ifs <;> simpa using hy'
  have haorth : a.slope d₁ = 0 := by
    dsimp [d₁]
    split_ifs <;> simp [Row.slope, tangent] <;> ring
  have hf₁ : target.slope d₁ ≤ 0 := by
    dsimp [d₁]
    split_ifs with h
    · exact h
    · have he : target.slope (fun i => -tangent i) = -target.slope tangent := by
        unfold Row.slope
        ring
      rw [he]
      exact neg_nonpos.mpr (le_of_not_ge h)
  obtain ⟨t₁, ht₁, b, hb, hbd, hb0, hq⟩ := first_exit rows box p₁ d₁ hp₁ hd₁
  let q := advance p₁ d₁ t₁
  have hab : det a b ≠ 0 := by
    intro hn
    have hn' : (a.x : ℝ) * b.y - (a.y : ℝ) * b.x = 0 := by
      dsimp [det] at hn
      exact_mod_cast hn
    have hz : b.slope d₁ = 0 := by
      dsimp [d₁]
      split_ifs <;> dsimp [Row.slope, tangent] <;> nlinarith only [hn']
    linarith only [hbd, hz]
  refine ⟨a, ha, b, hb, q, hab, ?_, hb0, hq, ?_⟩
  · dsimp [q]
    rw [eval_advance, haorth]
    simpa [p₁] using ha0
  · have hsecond : target.eval q ≤ target.eval p₁ := by
      dsimp [q]
      rw [eval_advance]
      have hm := mul_nonpos_of_nonneg_of_nonpos ht₁ hf₁
      linarith only [hm]
    exact hsecond.trans hfirst

def Feasible (base : List Row) (forbidden : List (List Row)) (p : Point) : Prop :=
  (∀ r ∈ base, 0 ≤ r.eval p) ∧
    ∀ block ∈ forbidden, ¬(∀ r ∈ block, 0 < r.eval p)

/-- The only numerical obligation: check each feasible intersection of two
original boundary lines. No polygon union, edge coverage, or sampled point
is accepted as a replacement for this universal finite boundary condition. -/
def VertexBound (base : List Row) (forbidden : List (List Row)) (target : Row) : Prop :=
  ∀ a ∈ base ++ forbidden.flatten, ∀ b ∈ base ++ forbidden.flatten,
    det a b ≠ 0 → ∀ p : Point,
      a.eval p = 0 → b.eval p = 0 → Feasible base forbidden p → 0 ≤ target.eval p

theorem nonnegative_of_vertices (base : List Row) (forbidden : List (List Row))
    (box : BoxNormals base) (target : Row) (checked : VertexBound base forbidden target)
    (p : Point) (hp : Feasible base forbidden p) : 0 ≤ target.eval p := by
  classical
  let outside := forbidden.flatten.filter (fun r => decide (r.eval p ≤ 0))
  let rows := base ++ outside.map negate
  have base_mem : ∀ r ∈ base, r ∈ rows := fun r hr => List.mem_append_left _ hr
  have box' : BoxNormals rows := box.mono base_mem
  have hp' : ∀ r ∈ rows, 0 ≤ r.eval p := by
    intro r hr
    rcases List.mem_append.mp hr with hb | ho
    · exact hp.1 r hb
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
      have hs' : s.eval p ≤ 0 := of_decide_eq_true (List.mem_filter.mp hs).2
      rw [eval_negate]
      linarith only [hs']
  have feasible : ∀ q : Point, (∀ r ∈ rows, 0 ≤ r.eval q) → Feasible base forbidden q := by
    intro q hq
    refine ⟨fun r hr => hq r (base_mem r hr), ?_⟩
    intro block hb hall
    have hn := hp.2 block hb
    push_neg at hn
    obtain ⟨r, hr, hrv⟩ := hn
    have hout : r ∈ outside := List.mem_filter.mpr
      ⟨List.mem_flatten.mpr ⟨block, hb, hr⟩, by simpa using hrv⟩
    have hneg : negate r ∈ rows := List.mem_append_right _ (List.mem_map.mpr ⟨r, hout, rfl⟩)
    have hh := hq (negate r) hneg
    rw [eval_negate] at hh
    linarith only [hh, hall r hr]
  have source : ∀ r ∈ rows, ∃ s ∈ base ++ forbidden.flatten, r = s ∨ r = negate s := by
    intro r hr
    rcases List.mem_append.mp hr with hb | ho
    · exact ⟨r, List.mem_append_left _ hb, Or.inl rfl⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ho
      exact ⟨s, List.mem_append_right _ (List.mem_filter.mp hs).1, Or.inr rfl⟩
  obtain ⟨a, ha, b, hb, q, hab, haq, hbq, hq, hmin⟩ := vertex_below rows box' target p hp'
  obtain ⟨a₀, ha₀, haeq⟩ := source a ha
  obtain ⟨b₀, hb₀, hbeq⟩ := source b hb
  have hfq := feasible q hq
  have ha₀q : a₀.eval q = 0 := by
    rcases haeq with he | he
    · simpa only [he] using haq
    · rw [he, eval_negate] at haq
      linarith only [haq]
  have hb₀q : b₀.eval q = 0 := by
    rcases hbeq with he | he
    · simpa only [he] using hbq
    · rw [he, eval_negate] at hbq
      linarith only [hbq]
  have hab₀ : det a₀ b₀ ≠ 0 := by
    intro hz
    apply hab
    rcases haeq with he | he <;> rcases hbeq with hf | hf <;>
      rw [he, hf] <;> simp [hz]
  have bound : 0 ≤ target.eval q := checked a₀ ha₀ b₀ hb₀ hab₀ q ha₀q hb₀q hfq
  exact bound.trans hmin

#print axioms nonnegative_of_vertices
end N12Compact.PlanarVertex
