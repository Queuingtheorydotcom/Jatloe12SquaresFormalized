import S12.DirectSingleDomain

namespace S12Completion.DomainReuse
open S12 S12Pilot

/-- The family enters a local domain check only through its auxiliary budget. -/
theorem direct_check_transport (w : DirectSingleDomain) (a b : Finset Nat)
    (k : Fin 2) (h : (a ∩ auxExempt k).card = (b ∩ auxExempt k).card)
    (hw : w.Check a k) : w.Check b k := by
  simpa only [DirectSingleDomain.Check, h] using hw

/-- Apply already proved local exclusions without duplicating their geometry.
The metadata check binds every query to the actual target mask and table. -/
def refineQueries {f : Finset Nat} (d : CertifiedDomain f)
    (qs : List {q : LocalQuery // q.Check})
    (hq : ∀ q ∈ qs, q.val.mask = d.mask ∧ q.val.kind = 2) : CertifiedDomain f :=
  ⟨d.mask, d.allowed.filter (fun x => decide (∀ q ∈ qs, x ≠ q.val.owned)), by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi, decide_eq_true ?_⟩
    intro q hmem he
    obtain ⟨hm, hk⟩ := hq q hmem
    exact q.val.sound q.property (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [hm, hi] using coded_exact p i)
      (by simpa only [hk, he] using nat_combined_exact p i)⟩

end S12Completion.DomainReuse
