import S12.DomainRefinement
import S12.DomainEnumeration
import S12.DirectSingleDomain
import Compact.Bridge.OwnerBudget

/-! Reuse geometric owner refutations with a new authentic family budget,
then refine their actual owner domains without assuming global auxiliary
ownership. Every refinement retains the full actual F/G subset. -/
namespace N12Compact.Completion.OtherCases.DomainTransport
open S12
set_option Elab.async false

theorem rebase (w : DirectSingleDomain) (oldFamily newFamily : Finset Nat)
    (k : Fin 2) (checked : w.Check oldFamily k)
    (lower : w.lower = if w.mask ∈ auxExempt k then 0 else 1)
    (upper : w.upper = (newFamily ∩ auxExempt k).card - 2 + w.lower) :
    w.Check newFamily k :=
  ⟨lower,upper,checked.2.2⟩

/-- A smaller authentic auxiliary budget permits reuse of every old local
refutation. Larger original ownership allowances are never assumed absent. -/
def restrictUpper (w : DirectSingleDomain) (upper : Nat) : DirectSingleDomain :=
  ⟨w.mask,w.lower,upper,w.allowed.filter (fun s => decide (s.card ≤ upper)),w.queries⟩

theorem restrictUpper_checked (w : DirectSingleDomain)
    (oldFamily newFamily : Finset Nat) (k : Fin 2)
    (checked : w.Check oldFamily k) (upper : Nat) (small : upper ≤ w.upper)
    (budget : upper = (newFamily ∩ auxExempt k).card - 2 + w.lower) :
    (restrictUpper w upper).Check newFamily k := by
  refine ⟨checked.1,budget,?_⟩
  intro s member low high
  rcases checked.2.2 s member low (high.trans small) with allowed | excluded
  · exact Or.inl (List.mem_filter.mpr ⟨allowed,decide_eq_true high⟩)
  · exact Or.inr excluded

/-- Remove only exact combined labels refuted by a certified geometric
query. The complete actual subset is passed to the original query theorem. -/
def trim {family : Finset Nat} (d : CertifiedDomain family)
    (queries : List {q : LocalQuery // q.Check})
    (matching : ∀ q ∈ queries, q.val.mask = d.mask ∧ q.val.kind = 2) :
    CertifiedDomain family :=
  ⟨d.mask,d.allowed.filter (fun s => decide (∀ q ∈ queries, s ≠ q.val.owned)),by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi,decide_eq_true ?_⟩
    intro q hq equal
    obtain ⟨mask,kind⟩ := matching q hq
    exact q.val.sound q.property (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [mask,hi] using coded_exact p i)
      (by simpa only [kind,equal] using nat_combined_exact p i)⟩

/-- A compulsory seed-hull point determines an auxiliary singleton when
the authentic budget permits at most one point, including an exempt owner
whose lower budget is zero. -/
def hullSingleton (family : Finset Nat) (mask : Nat) (k : Fin 2) (index : Nat)
    (indexBound : index < 10)
    (upper : (family ∩ auxExempt k).card - 2 + (if mask ∈ auxExempt k then 0 else 1) = 1)
    (w : TriangleCertificate) (checked : w.Check)
    (target : w.target = (auxPoints (auxKind k))[index]!)
    (first : w.p0 ∈ seedPoints (maskSupport mask))
    (second : w.p1 ∈ seedPoints (maskSupport mask))
    (third : w.p2 ∈ seedPoints (maskSupport mask)) :
    N12Compact.OwnerBudget.HalfDomain family mask k :=
  ⟨[{index}],by
    intro p i hf hi
    have budget := nat_aux_budget p k i
    rw [hf,hi,upper] at budget
    have seeds := seed_points_sound (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (maskSupport mask) (by simpa only [hi] using coded_exact p i)
    have inside := triangle_certificate_sound w checked (p.square i)
      (seeds _ first) (seeds _ second) (seeds _ third)
    rw [target] at inside
    have member := (nat_aux_exact p k i index
      (by rw [aux_kind_length]; exact List.mem_range.mpr indexBound)).mp inside
    have card : (natAuxOwners p k i).card = 1 :=
      le_antisymm budget.2 (Finset.one_le_card.mpr ⟨index,member⟩)
    obtain ⟨j,equal⟩ := Finset.card_eq_one.mp card
    have same : index = j := by simpa only [equal,Finset.mem_singleton] using member
    simpa only [List.mem_singleton,same] using equal⟩

structure NamedDomain (family : Finset Nat) where
  val : CertifiedDomain family
  member : val.mask ∈ family

def NamedDomain.refine {family : Finset Nat}
    (a b : NamedDomain family) : NamedDomain family :=
  if same : a.val.mask = b.val.mask then a
  else ⟨a.val.refineAgainst b.val b.member same, a.member⟩

theorem NamedDomain.refine_mask {family : Finset Nat}
    (a b : NamedDomain family) : (a.refine b).val.mask = a.val.mask := by
  unfold NamedDomain.refine
  split_ifs <;> rfl

def sweep {family : Finset Nat} (ds : List (NamedDomain family)) :
    List (NamedDomain family) :=
  ds.map fun d => ds.foldl NamedDomain.refine d

theorem fold_refine_mask {family : Finset Nat} (a : NamedDomain family)
    (ds : List (NamedDomain family)) :
    (ds.foldl NamedDomain.refine a).val.mask = a.val.mask := by
  induction ds generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simpa only [List.foldl_cons,NamedDomain.refine_mask] using ih (a.refine b)

theorem sweep_masks {family : Finset Nat} (ds : List (NamedDomain family)) :
    (sweep ds).map (fun d => d.val.mask) = ds.map (fun d => d.val.mask) := by
  simp only [sweep,List.map_map]
  apply List.map_congr_left
  intro d _
  exact fold_refine_mask d ds

theorem actual_vector_eq_of_masks {family : Finset Nat}
    (ds es : List (CertifiedDomain family))
    (same : ds.map CertifiedDomain.mask = es.map CertifiedDomain.mask)
    (p : NormalizedPacking) :
    ds.map (fun d => natCombinedOwners p (ownerIndex p d.mask)) =
      es.map (fun d => natCombinedOwners p (ownerIndex p d.mask)) := by
  have h := congrArg (List.map (fun m => natCombinedOwners p (ownerIndex p m))) same
  simpa only [List.map_map] using h

end N12Compact.Completion.OtherCases.DomainTransport
