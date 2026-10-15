import Compact.Bridge.SmallOwnerDomainThree

/-! A certified local rejection remains valid when more auxiliaries are
owned, provided all of the certificate's actual foreign auxiliaries remain
absent. This symbolic adapter lets C983 retain its authentic upper budget
of three without one cloned certificate for every enlarged label. -/
namespace N12Compact.Completion.OtherCases.MonotoneQueries
open S12 S12Pilot
set_option Elab.async false

def neededOutside : LocalRejection → List (ℚ × ℚ)
  | .hull w => [w.target]
  | .short k _ => k.outsidePoints
  | .four t w _ => [t.applyRat w.p,t.applyRat w.e]

private theorem hull_check_mono (old next : List (ℚ × ℚ)) (w : TriangleCertificate)
    (checked : HullInCheck old w) (included : ∀ p ∈ old, p ∈ next) :
    HullInCheck next w :=
  ⟨checked.1,included _ checked.2.1,included _ checked.2.2.1,included _ checked.2.2.2⟩

theorem needed_outside_mem (certificate : LocalRejection)
    (inside outside : List (ℚ × ℚ)) (checked : certificate.Check inside outside) :
    ∀ p ∈ neededOutside certificate, p ∈ outside := by
  cases certificate with
  | hull w =>
      intro p member
      have equality : p=w.target := by simpa only [neededOutside,List.mem_singleton] using member
      subst p
      exact checked.2
  | short k ws => exact checked.2
  | four t w hw =>
      intro p member
      simp only [neededOutside,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact checked.2.2.1
      · exact checked.2.2.2

theorem check_mono (certificate : LocalRejection)
    (oldInside oldOutside nextInside nextOutside : List (ℚ × ℚ))
    (checked : certificate.Check oldInside oldOutside)
    (inside : ∀ p ∈ oldInside, p ∈ nextInside)
    (outside : ∀ p ∈ neededOutside certificate, p ∈ nextOutside) :
    certificate.Check nextInside nextOutside := by
  cases certificate with
  | hull w =>
      exact ⟨hull_check_mono _ _ _ checked.1 inside,
        outside _ (by simp [neededOutside])⟩
  | short k ws =>
      refine ⟨?_,outside⟩
      intro p member
      obtain ⟨w,hw,equal,hull⟩ := checked.1 p member
      exact ⟨w,hw,equal,hull_check_mono _ _ _ hull inside⟩
  | four t w hw =>
      exact ⟨inside _ checked.1,inside _ checked.2.1,
        outside _ (by simp [neededOutside]),outside _ (by simp [neededOutside])⟩

def blocked (query : LocalQuery) : Finset Nat :=
  (List.range (auxPoints query.kind).length).toFinset.filter
    (fun i => (auxPoints query.kind)[i]! ∈ neededOutside query.certificate)

private theorem inside_mono (mask : Nat) (kind : Fin 3) (old next : Finset Nat)
    (subset : old ⊆ next) :
    ∀ p ∈ queryInsidePoints mask kind old, p ∈ queryInsidePoints mask kind next := by
  intro p member
  rcases List.mem_append.mp member with seed | auxiliary
  · exact List.mem_append_left _ seed
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp auxiliary
    obtain ⟨range,owned⟩ := List.mem_filter.mp hi
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨i,List.mem_filter.mpr ⟨range,decide_eq_true (subset (of_decide_eq_true owned))⟩,rfl⟩

private theorem outside_mono (query : LocalQuery) (checked : query.Check) (next : Finset Nat)
    (apart : Disjoint next (blocked query)) :
    ∀ p ∈ neededOutside query.certificate, p ∈ queryOutsidePoints query.mask query.kind next := by
  intro p needed
  have member := needed_outside_mem query.certificate _ _ checked p needed
  rcases List.mem_append.mp member with marker | auxiliary
  · exact List.mem_append_left _ marker
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp auxiliary
    have range := (List.mem_filter.mp hi).1
    have blockedMember : i ∈ blocked query :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr range,needed⟩
    have missing : i ∉ next := fun owned =>
      Finset.disjoint_left.mp apart owned blockedMember
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨i,List.mem_filter.mpr ⟨range,decide_eq_true missing⟩,rfl⟩

def extended (query : LocalQuery) (owned : Finset Nat) : LocalQuery :=
  ⟨query.mask,query.kind,owned,query.certificate⟩

theorem extended_checked (query : LocalQuery) (checked : query.Check)
    (owned : Finset Nat) (subset : query.owned ⊆ owned)
    (apart : Disjoint owned (blocked query)) : (extended query owned).Check :=
  check_mono query.certificate _ _ _ _ checked
    (inside_mono query.mask query.kind query.owned owned subset)
    (outside_mono query checked owned apart)

/-- The enlarged query concerns this actual square and its actual full
auxiliary ownership set. It reuses only the old certificate's geometry. -/
theorem extended_sound (query : LocalQuery) (checked : query.Check)
    (owned : Finset Nat) (subset : query.owned ⊆ owned)
    (apart : Disjoint owned (blocked query)) (q : OpenSquare)
    (side : 1 < q.side) (cap : q.side ≤ 1001/1000) (box : InsideContainer q)
    (markers : ExactMarkers q (maskSupport query.mask))
    (auxiliary : AuxExact q query.kind owned) : False :=
  (extended query owned).sound (extended_checked query checked owned subset apart)
    q side cap box markers auxiliary

abbrev Signature := Nat × Fin 3 × Finset Nat × Finset Nat

def signature (query : LocalQuery) : Signature :=
  (query.mask,query.kind,query.owned,blocked query)

def compatible (entry : Signature) (mask : Nat) (kind : Fin 2) (owned : Finset Nat) : Prop :=
  entry.1=mask ∧ entry.2.1=auxKind kind ∧ entry.2.2.1 ⊆ owned ∧
    Disjoint owned entry.2.2.2

instance (entry : Signature) (mask : Nat) (kind : Fin 2) (owned : Finset Nat) :
    Decidable (compatible entry mask kind owned) := by
  unfold compatible
  infer_instance

/-- Only the finite scalar signature enters the membership check. -/
structure SingleDomain where
  mask : Nat
  lower : Nat
  upper : Nat
  allowed : List (Finset Nat)
  queries : List {query : LocalQuery // query.Check}

def SingleDomain.Check (w : SingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Prop :=
  w.lower=(if w.mask∈auxExempt kind then 0 else 1) ∧
  w.upper=(family∩auxExempt kind).card-2+w.lower ∧ w.upper≤3 ∧
  ∀ owned ∈ SmallOwnerDomainThree.smallSubsetsThree,
    w.lower≤owned.card → owned.card≤w.upper →
      owned∈w.allowed ∨ ∃ entry∈signatures,compatible entry w.mask kind owned

instance (w : SingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature) : Decidable (w.Check family kind signatures) := by
  unfold SingleDomain.Check
  letI : Decidable (∀ owned ∈ SmallOwnerDomainThree.smallSubsetsThree,
    w.lower≤owned.card → owned.card≤w.upper →
      owned∈w.allowed ∨ ∃ entry∈signatures,compatible entry w.mask kind owned) :=
    List.decidableBAll _ SmallOwnerDomainThree.smallSubsetsThree
  infer_instance

theorem SingleDomain.actual (w : SingleDomain) (family : Finset Nat) (kind : Fin 2)
    (signatures : List Signature)
    (exactSignatures : signatures=w.queries.map (fun query => signature query.val))
    (checked : w.Check family kind signatures)
    (p : NormalizedPacking) (i : Fin 12)
    (familyExact : codedMarkerFamily p=family) (maskExact : markerCode p i=w.mask) :
    natAuxOwners p kind i∈w.allowed := by
  classical
  let actual := natAuxOwners p kind i
  have budget := nat_aux_budget p kind i
  rw [familyExact,maskExact] at budget
  have low : w.lower≤actual.card := by simpa only [checked.1] using budget.1
  have high : actual.card≤w.upper := by simpa only [checked.2.1,checked.1] using budget.2
  have small := SmallOwnerDomainThree.smallSubsetsThree_complete actual
    (nat_aux_subset p kind i) (high.trans checked.2.2.1)
  rcases checked.2.2.2 actual small low high with allowed | excluded
  · exact allowed
  · obtain ⟨entry,member,hm,hk,anchors,missing⟩ := excluded
    rw [exactSignatures] at member
    obtain ⟨query,_,equal⟩ := List.mem_map.mp member
    subst entry
    change query.val.mask=w.mask at hm
    change query.val.kind=auxKind kind at hk
    change query.val.owned⊆actual at anchors
    change Disjoint actual (blocked query.val) at missing
    apply False.elim
    apply extended_sound query.val query.property actual anchors missing (p.square i)
    · rw [p.congruent]; exact p.side_gt_one
    · rw [p.congruent]; exact p.side_le
    · exact p.contained i
    · simpa only [hm,maskExact] using coded_exact p i
    · simpa only [hk] using nat_aux_exact p kind i

def product (family : Finset Nat) (f g : SingleDomain)
    (fSignatures gSignatures : List Signature)
    (fExact : fSignatures=f.queries.map (fun q => signature q.val))
    (gExact : gSignatures=g.queries.map (fun q => signature q.val))
    (fChecked : f.Check family 0 fSignatures) (gChecked : g.Check family 1 gSignatures)
    (sameMask : f.mask=g.mask) : CertifiedDomain family :=
  ⟨f.mask,f.allowed.flatMap (fun x => g.allowed.map (combinedOwners x)),by
    intro p i familyExact maskExact
    exact List.mem_flatMap.mpr
      ⟨_,f.actual family 0 fSignatures fExact fChecked p i familyExact maskExact,
        List.mem_map.mpr
          ⟨_,g.actual family 1 gSignatures gExact gChecked p i familyExact (maskExact.trans sameMask),rfl⟩⟩⟩

#print axioms SingleDomain.actual
end N12Compact.Completion.OtherCases.MonotoneQueries

