import S12.CertifiedDomain
namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- A portable finite owner-domain certificate using explicitly typed local proofs. -/
structure DirectSingleDomain where
  mask : Nat
  lower : Nat
  upper : Nat
  allowed : List (Finset Nat)
  queries : List {q : LocalQuery // q.Check}

def DirectSingleDomain.Check (w : DirectSingleDomain) (family : Finset Nat) (k : Fin 2) : Prop :=
  w.lower=(if w.mask∈auxExempt k then 0 else 1) ∧
  w.upper=(family∩auxExempt k).card-2+w.lower ∧
  ∀ x∈allAuxSubsets,w.lower≤x.card → x.card≤w.upper →
    x∈w.allowed ∨ ∃ q∈w.queries,q.val.mask=w.mask ∧ q.val.kind=auxKind k ∧ q.val.owned=x
instance DirectSingleDomain.decidableCheck (w : DirectSingleDomain) (family : Finset Nat) (k : Fin 2) :
    Decidable (w.Check family k) := inferInstanceAs (Decidable (_ ∧ _))

theorem DirectSingleDomain.actual (w : DirectSingleDomain) (family : Finset Nat) (k : Fin 2)
    (hw : w.Check family k) (p : NormalizedPacking) (i : Fin 12)
    (hf : codedMarkerFamily p=family) (hm : markerCode p i=w.mask) :
    natAuxOwners p k i∈w.allowed := by
  have hb := nat_aux_budget p k i
  rw [hf,hm] at hb
  have hlo : w.lower≤(natAuxOwners p k i).card := by simpa only [hw.1] using hb.1
  have hhi : (natAuxOwners p k i).card≤w.upper := by simpa only [hw.2.1,hw.1] using hb.2
  rcases hw.2.2 _ (allAuxSubsets_complete _ (nat_aux_subset p k i)) hlo hhi with h | h
  · exact h
  · obtain ⟨q,_,hmask,hkind,howned⟩ := h
    exact False.elim (q.val.sound q.property (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one) (by rw [p.congruent]; exact p.side_le)
      (p.contained i) (by simpa only [hmask,hm] using coded_exact p i)
      (by simpa only [hkind,howned] using nat_aux_exact p k i))

def CertifiedDomain.ofDirectProduct (family : Finset Nat) (a b : DirectSingleDomain)
    (ha : a.Check family 0) (hb : b.Check family 1) (he : a.mask=b.mask) : CertifiedDomain family :=
  ⟨a.mask,a.allowed.flatMap (fun x => b.allowed.map (combinedOwners x)),by
    intro p i hf hi
    exact List.mem_flatMap.mpr ⟨_,a.actual family 0 ha p i hf hi,
      List.mem_map.mpr ⟨_,b.actual family 1 hb p i hf (hi.trans he),rfl⟩⟩⟩

#print axioms DirectSingleDomain.actual
end S12
