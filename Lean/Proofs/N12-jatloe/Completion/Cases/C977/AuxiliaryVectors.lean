import Completion.Cases.C977.CornerRoots
import S12.CoreExclusion
import S12.DomainSpecData

/-! Exhaustive case-977 auxiliary ownership in the historical sorted F/G order.
The owner permutation is derived from the complete actual marker family. The
finite cover records every actual ownership set, including empty exempt sets
and all boundary exclusions. Historical source-data checks retain their
inherited native compiler trust; this module introduces no native sites.

Route attribution: Jatloe-12-squares-reconstruction b99f388c8469cc756960576809004e1806c51e3a,
machine-assisted-proof/src/verify_case_977.py and CASE_977.md. The original
auxiliary tables and geometric certificates remain unchanged. -/
namespace S12Completion.C977
open S12 S12Pilot
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pairQuery0 : LocalQuery := ⟨12,0,{0},.four ⟨true,true,false⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery1 : LocalQuery := ⟨12,0,{1},.four ⟨true,true,false⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery2 : LocalQuery := ⟨12,0,{2},.four ⟨true,true,false⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery3 : LocalQuery := ⟨12,0,{3},.four ⟨false,true,false⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery4 : LocalQuery := ⟨12,0,{4},.four ⟨true,true,false⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery5 : LocalQuery := ⟨12,0,{5},.four ⟨false,true,false⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery6 : LocalQuery := ⟨12,0,{7},.four ⟨false,true,false⟩ fourDatum2 fourDatum2_checked⟩
def pairQuery7 : LocalQuery := ⟨12,0,{9},.four ⟨false,true,false⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery8 : LocalQuery := ⟨12,1,{0},.four ⟨true,true,false⟩ fourDatum2 fourDatum2_checked⟩
def pairQuery9 : LocalQuery := ⟨12,1,{1},.four ⟨true,true,false⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery10 : LocalQuery := ⟨12,1,{2},.four ⟨true,true,false⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery11 : LocalQuery := ⟨12,1,{3},.four ⟨true,true,false⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery12 : LocalQuery := ⟨12,1,{4},.four ⟨false,true,false⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery13 : LocalQuery := ⟨12,1,{6},.four ⟨false,true,false⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery14 : LocalQuery := ⟨12,1,{7},.four ⟨false,true,false⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery15 : LocalQuery := ⟨12,1,{9},.four ⟨false,true,false⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery16 : LocalQuery := ⟨48,0,{0},.four ⟨true,true,true⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery17 : LocalQuery := ⟨48,0,{1},.four ⟨true,true,true⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery18 : LocalQuery := ⟨48,0,{2},.four ⟨false,true,true⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery19 : LocalQuery := ⟨48,0,{3},.four ⟨true,true,true⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery20 : LocalQuery := ⟨48,0,{4},.four ⟨false,true,true⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery21 : LocalQuery := ⟨48,0,{5},.four ⟨true,true,true⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery22 : LocalQuery := ⟨48,0,{6},.four ⟨false,true,true⟩ fourDatum2 fourDatum2_checked⟩
def pairQuery23 : LocalQuery := ⟨48,0,{8},.four ⟨false,true,true⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery24 : LocalQuery := ⟨48,1,{0},.four ⟨true,true,true⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery25 : LocalQuery := ⟨48,1,{1},.four ⟨true,true,true⟩ fourDatum2 fourDatum2_checked⟩
def pairQuery26 : LocalQuery := ⟨48,1,{2},.four ⟨false,true,true⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery27 : LocalQuery := ⟨48,1,{3},.four ⟨true,true,true⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery28 : LocalQuery := ⟨48,1,{4},.four ⟨true,true,true⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery29 : LocalQuery := ⟨48,1,{5},.four ⟨false,true,true⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery30 : LocalQuery := ⟨48,1,{6},.four ⟨false,true,true⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery31 : LocalQuery := ⟨48,1,{8},.four ⟨false,true,true⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery32 : LocalQuery := ⟨192,0,{0},.four ⟨false,false,true⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery33 : LocalQuery := ⟨192,0,{2},.four ⟨false,false,true⟩ fourDatum2 fourDatum2_checked⟩
def pairQuery34 : LocalQuery := ⟨192,0,{4},.four ⟨false,false,true⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery35 : LocalQuery := ⟨192,0,{5},.four ⟨true,false,true⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery36 : LocalQuery := ⟨192,0,{6},.four ⟨false,false,true⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery37 : LocalQuery := ⟨192,0,{7},.four ⟨true,false,true⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery38 : LocalQuery := ⟨192,0,{8},.four ⟨true,false,true⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery39 : LocalQuery := ⟨192,0,{9},.four ⟨true,false,true⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery40 : LocalQuery := ⟨192,1,{0},.four ⟨false,false,true⟩ fourDatum1 fourDatum1_checked⟩
def pairQuery41 : LocalQuery := ⟨192,1,{2},.four ⟨false,false,true⟩ fourDatum7 fourDatum7_checked⟩
def pairQuery42 : LocalQuery := ⟨192,1,{3},.four ⟨false,false,true⟩ fourDatum5 fourDatum5_checked⟩
def pairQuery43 : LocalQuery := ⟨192,1,{5},.four ⟨false,false,true⟩ fourDatum9 fourDatum9_checked⟩
def pairQuery44 : LocalQuery := ⟨192,1,{6},.four ⟨true,false,true⟩ fourDatum8 fourDatum8_checked⟩
def pairQuery45 : LocalQuery := ⟨192,1,{7},.four ⟨true,false,true⟩ fourDatum0 fourDatum0_checked⟩
def pairQuery46 : LocalQuery := ⟨192,1,{8},.four ⟨true,false,true⟩ fourDatum10 fourDatum10_checked⟩
def pairQuery47 : LocalQuery := ⟨192,1,{9},.four ⟨true,false,true⟩ fourDatum2 fourDatum2_checked⟩


variable {P : Type} [DecidableEq P]

/-- Enumerate domain vectors in the original owner order, pruning only overlap
with previously used points. -/
def enumerateVectors : List (List (Finset P)) → Finset P → List (List (Finset P))
  | [], _ => [[]]
  | d :: ds, used => d.flatMap fun m =>
      if Disjoint m used then (enumerateVectors ds (used ∪ m)).map (m :: ·) else []

/-- Complete actual owner vectors belong to the fixed-order enumeration. -/
theorem actual_owners_mem_enumerateVectors
    (ds : List (List (Finset P))) (owners : List (Finset P)) (used : Finset P)
    (hmem : List.Forall₂ (fun m d => m ∈ d) owners ds)
    (hused : ∀ m ∈ owners, Disjoint m used)
    (hdis : owners.Pairwise Disjoint) : owners ∈ enumerateVectors ds used := by
  induction hmem generalizing used with
  | nil => simp [enumerateVectors]
  | @cons m d owners ds hm hmem ih =>
    obtain ⟨hmrest, hrest⟩ := List.pairwise_cons.mp hdis
    have hd : Disjoint m used := hused m (by simp)
    have ht : owners ∈ enumerateVectors ds (used ∪ m) := by
      apply ih
      · intro n hn
        exact Finset.disjoint_union_right.mpr
          ⟨hused n (by simp [hn]), (hmrest n hn).symm⟩
      · exact hrest
    simp only [enumerateVectors, List.mem_flatMap]
    refine ⟨m, hm, ?_⟩
    simp only [hd, if_pos, List.mem_map]
    exact ⟨owners, ht, rfl⟩



def countVectors : List (List (Finset P)) → Finset P → Nat
  | [], _ => 1
  | d :: ds, used => (d.map fun m =>
      if Disjoint m used then countVectors ds (used ∪ m) else 0).sum

/-- The recursive count is exactly the length of the complete enumerator. -/
theorem enumerateVectors_length (ds : List (List (Finset P))) (used : Finset P) :
    (enumerateVectors ds used).length = countVectors ds used := by
  induction ds generalizing used with
  | nil => rfl
  | cons d ds ih =>
    simp only [enumerateVectors, countVectors, List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro m hm
    split_ifs with hd
    · exact (List.length_map _).trans (ih (used ∪ m))
    · rfl

/-- Distinct entries in each owner domain produce distinct complete vectors. -/
theorem enumerateVectors_nodup
    (ds : List (List (Finset P))) (used : Finset P)
    (h : ∀ d ∈ ds, d.Nodup) : (enumerateVectors ds used).Nodup := by
  induction ds generalizing used with
  | nil => simp [enumerateVectors]
  | cons d ds ih =>
    have hd : d.Nodup := h d (by simp)
    have hds : ∀ e ∈ ds, e.Nodup := fun e he => h e (by simp [he])
    simp only [enumerateVectors]
    apply List.nodup_flatMap.mpr
    constructor
    · intro m hm
      split_ifs with hmused
      · exact (ih (used ∪ m) hds).map (fun _ _ he => (List.cons.inj he).2)
      · exact List.nodup_nil
    · apply hd.imp
      intro m n hmn
      change List.Disjoint
        (if Disjoint m used then
          (enumerateVectors ds (used ∪ m)).map (m :: ·) else [])
        (if Disjoint n used then
          (enumerateVectors ds (used ∪ n)).map (n :: ·) else [])
      split_ifs with hmused hnused
      · apply List.disjoint_left.mpr
        intro v hv hv'
        obtain ⟨ms, _, hms⟩ := List.mem_map.mp hv
        obtain ⟨ns, _, hns⟩ := List.mem_map.mp hv'
        exact hmn (List.cons.inj (hms.trans hns.symm)).1
      · simp
      · simp
      · simp


def pairCode (i : Fin 3) : Nat := ![12, 48, 192] i

def pairSingleAllowed (i : Fin 3) (k : Fin 2) : List (Finset Nat) :=
  match i.val, k.val with
  | 0, 0 => [∅, {6}, {8}]
  | 0, _ => [∅, {5}, {8}]
  | 1, _ => [∅, {7}, {9}]
  | _, 0 => [∅, {1}, {3}]
  | _, _ => [∅, {1}, {4}]

def pairQueries (i : Fin 3) (k : Fin 2) : List LocalQuery :=
  match i.val, k.val with
  | 0, 0 => [pairQuery0,pairQuery1,pairQuery2,pairQuery3,pairQuery4,pairQuery5,pairQuery6,pairQuery7]
  | 0, _ => [pairQuery8,pairQuery9,pairQuery10,pairQuery11,pairQuery12,pairQuery13,pairQuery14,pairQuery15]
  | 1, 0 => [pairQuery16,pairQuery17,pairQuery18,pairQuery19,pairQuery20,pairQuery21,pairQuery22,pairQuery23]
  | 1, _ => [pairQuery24,pairQuery25,pairQuery26,pairQuery27,pairQuery28,pairQuery29,pairQuery30,pairQuery31]
  | _, 0 => [pairQuery32,pairQuery33,pairQuery34,pairQuery35,pairQuery36,pairQuery37,pairQuery38,pairQuery39]
  | _, _ => [pairQuery40,pairQuery41,pairQuery42,pairQuery43,pairQuery44,pairQuery45,pairQuery46,pairQuery47]

theorem pair_queries_checked (i : Fin 3) (k : Fin 2) :
    ∀ w ∈ pairQueries i k, w.Check := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem pair_empty_allowed (i : Fin 3) (k : Fin 2) :
    (∅ : Finset Nat) ∈ pairSingleAllowed i k := by
  fin_cases i <;> fin_cases k <;> decide +kernel

/-- All ten possible singleton sets are covered by an allowed set or an
    explicit checked local geometric contradiction. -/
theorem pair_singleton_cover (i : Fin 3) (k : Fin 2) (j : Fin 10) :
    ({j.val} : Finset Nat) ∈ pairSingleAllowed i k ∨
      ∃ w ∈ pairQueries i k,
        w.mask = pairCode i ∧ w.kind = auxKind k ∧ w.owned = {j.val} := by
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide +kernel

/-- The three corner-pair owners are exactly the F/G exemptions in this
    family. Its slack is one, so each of them owns at most one F point and
    at most one G point. -/
theorem pair_budget_identity (i : Fin 3) (k : Fin 2) :
    pairCode i ∈ auxExempt k ∧ (family ∩ auxExempt k).card = 3 := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem pair_single_actual (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 3) (k : Fin 2) (j : Fin 12)
    (hc : markerCode p j = pairCode i) :
    natAuxOwners p k j ∈ pairSingleAllowed i k := by
  have hb := (nat_aux_budget p k j).2
  rw [hf, hc] at hb
  obtain ⟨hex, hcard⟩ := pair_budget_identity i k
  have hsmall : (natAuxOwners p k j).card ≤ 1 := by simpa [hex, hcard] using hb
  by_cases hz : natAuxOwners p k j = ∅
  · rw [hz]
    exact pair_empty_allowed i k
  have hpos : 0 < (natAuxOwners p k j).card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hz)
  have hone : (natAuxOwners p k j).card = 1 := by omega
  obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hone
  have hlt : n < 10 := Finset.mem_range.mp
    (nat_aux_subset p k j (by rw [hn]; simp))
  rcases pair_singleton_cover i k ⟨n,hlt⟩ with h | h
  · simpa only [hn] using h
  obtain ⟨w, hw, hm, hk, ho⟩ := h
  have ha : 1 < (p.square j).side := by rw [p.congruent]; exact p.side_gt_one
  have hs : (p.square j).side ≤ 1001/1000 := by rw [p.congruent]; exact p.side_le
  exact False.elim (w.sound (pair_queries_checked i k w hw) (p.square j) ha hs
    (p.contained j) (by simpa only [hc, hm] using coded_exact p j)
    (by simpa only [hk, ho, hn] using nat_aux_exact p k j))

def pairCombinedAllowed (i : Fin 3) : List (Finset Nat) :=
  (pairSingleAllowed i 0).flatMap fun x =>
    (pairSingleAllowed i 1).map fun y => combinedOwners x y

theorem pair_combined_actual (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 3) (j : Fin 12)
    (hc : markerCode p j = pairCode i) :
    natCombinedOwners p j ∈ pairCombinedAllowed i := by
  apply List.mem_flatMap.mpr
  refine ⟨natAuxOwners p 0 j, pair_single_actual p hf i 0 j hc, ?_⟩
  exact List.mem_map.mpr ⟨natAuxOwners p 1 j,
    pair_single_actual p hf i 1 j hc, rfl⟩

/-- Historical zero-based owner order; this is a code list, not an assumed
    order of the original square labels. -/
def auxiliaryCode (i : Fin 12) : Nat :=
  ![1,2,12,48,192,256,512,2048,4096,8192,16384,32768] i

theorem auxiliary_code_mem (i : Fin 12) : auxiliaryCode i ∈ family := by
  fin_cases i <;> decide +kernel

theorem auxiliary_code_injective : Function.Injective auxiliaryCode := by
  decide +kernel

/-- Select the unique original owner of each historical marker code. -/
noncomputable def orderedOwner (p : NormalizedPacking) (i : Fin 12) : Fin 12 :=
  ownerIndex p (auxiliaryCode i)

theorem ordered_owner_code (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    markerCode p (orderedOwner p i) = auxiliaryCode i := by
  apply ownerIndex_spec
  rw [hf]
  exact auxiliary_code_mem i

theorem ordered_owner_injective (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : Function.Injective (orderedOwner p) := by
  intro i j h
  apply auxiliary_code_injective
  exact (ordered_owner_code p hf i).symm.trans
    ((congrArg (markerCode p) h).trans (ordered_owner_code p hf j))

/-- All twelve original squares occur exactly once in the ordered vector. -/
theorem ordered_owner_bijective (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : Function.Bijective (orderedOwner p) :=
  ⟨ordered_owner_injective p hf,
    Finite.surjective_of_injective (ordered_owner_injective p hf)⟩

/-- Saved necessary domains for the nine nonexempt owners, together with
    the six proved single F/G domains for the three exempt pairs. -/
def auxiliaryDomain (i : Fin 12) : List (Finset Nat) :=
  match i.val with
  | 0 => combinedSpec1.allowed
  | 1 => combinedSpec3.allowed
  | 2 => pairCombinedAllowed 0
  | 3 => pairCombinedAllowed 1
  | 4 => pairCombinedAllowed 2
  | 5 => combinedSpec6.allowed
  | 6 => combinedSpec8.allowed
  | 7 => combinedSpec13.allowed
  | 8 => combinedSpec17.allowed
  | 9 => combinedSpec19.allowed
  | 10 => combinedSpec21.allowed
  | _ => combinedSpec24.allowed

theorem auxiliary_domain_actual (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    natCombinedOwners p (orderedOwner p i) ∈ auxiliaryDomain i := by
  have hc := ordered_owner_code p hf i
  fin_cases i
  · exact combinedSpec1.actual combinedSpec1_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec3.actual combinedSpec3_checked family (by decide +kernel)
      p _ hf hc
  · exact pair_combined_actual p hf 0 _ hc
  · exact pair_combined_actual p hf 1 _ hc
  · exact pair_combined_actual p hf 2 _ hc
  · exact combinedSpec6.actual combinedSpec6_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec8.actual combinedSpec8_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec13.actual combinedSpec13_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec17.actual combinedSpec17_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec19.actual combinedSpec19_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec21.actual combinedSpec21_checked family (by decide +kernel)
      p _ hf hc
  · exact combinedSpec24.actual combinedSpec24_checked family (by decide +kernel)
      p _ hf hc

def pruningDomain1 (i : Fin 12) : List (Finset Nat) :=
  match i.val with
  | 0 => [{2,12}]
  | 1 => [{0,10}]
  | 2 => [∅,{15},{18},{6},{6,15},{6,18},{8},{8,15},{8,18}]
  | 3 => [∅,{17},{19},{7},{7,17},{7,19},{9},{9,17},{9,19}]
  | 4 => [∅,{11},{14},{1},{1,11},{1,14},{3},{3,11},{3,14}]
  | 5 => [{4,13},{4,13,15},{4,13,16},{1,4,13},{1,4,13,15},{1,4,13,16},{4,5,13},{4,5,13,15},{4,5,13,16}]
  | 6 => [{4,15},{4,16},{4,18},{4,13,15},{4,13,16},{4,15,16},{4,15,18},{4,16,18},{6,15},{6,16},{6,18},{6,15,16},{6,15,18},{6,16,18},{8,15},{8,16},{8,18},{8,15,16},{8,15,18},{8,16,18},{4,5,16},{4,5,13,16},{4,5,15,16},{4,5,16,18},{4,6,15},{4,6,16},{4,6,18},{4,6,13,15},{4,6,13,16},{4,6,15,16},{4,6,15,18},{4,6,16,18},{4,8,15},{4,8,16},{4,8,18},{4,8,13,15},{4,8,13,16},{4,8,15,16},{4,8,15,18},{4,8,16,18},{4,9,16},{4,9,13,16},{4,9,15,16},{5,8,16},{5,8,15,16},{5,8,16,18},{6,8,15},{6,8,16},{6,8,18},{6,8,15,16},{6,8,15,18},{6,8,16,18}]
  | 7 => [{1,11},{1,13},{1,14},{1,11,13},{1,11,14},{1,13,14},{3,11},{3,13},{3,14},{3,11,13},{3,11,14},{3,13,14},{5,11},{5,13},{5,14},{5,11,13},{5,11,14},{5,13,14},{5,13,16},{5,13,17},{5,14,16},{1,3,11},{1,3,13},{1,3,14},{1,3,11,13},{1,3,11,14},{1,3,13,14},{1,4,13},{1,4,11,13},{1,4,13,14},{1,5,11},{1,5,13},{1,5,14},{1,5,11,13},{1,5,11,14},{1,5,13,14},{1,5,13,16},{1,5,13,17},{1,5,14,16},{3,5,11},{3,5,13},{3,5,14},{3,5,11,13},{3,5,11,14},{3,5,13,14},{3,5,13,16},{3,5,14,16},{4,5,13},{4,5,11,13},{4,5,13,14},{4,5,13,16},{4,5,13,17}]
  | 8 => [{1,11},{1,11,13},{1,3,11}]
  | 9 => [{6,15},{6,15,18},{4,6,15}]
  | 10 => [{8,18},{8,16,18},{9,19},{9,16,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19}]
  | _ => [{3,14},{3,11,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17}]

def pruningDomain2 (i : Fin 12) : List (Finset Nat) :=
  match i.val with
  | 0 => [{2,12}]
  | 1 => [{0,10}]
  | 2 => [∅,{18},{8},{8,18}]
  | 3 => [∅,{17},{19},{7},{7,17},{7,19},{9},{9,17},{9,19}]
  | 4 => [∅,{14},{3},{3,14}]
  | 5 => [{4,13},{4,13,16},{4,5,13},{4,5,13,16}]
  | 6 => [{8,16},{8,18},{8,16,18},{5,8,16},{5,8,16,18}]
  | 7 => [{3,14},{5,14},{5,14,16},{3,5,14},{3,5,14,16}]
  | 8 => [{1,11},{1,3,11}]
  | 9 => [{6,15},{6,15,18}]
  | 10 => [{8,18},{8,16,18},{9,19},{9,16,19},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19}]
  | _ => [{3,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17}]

def pruningDomain3 (i : Fin 12) : List (Finset Nat) :=
  match i.val with
  | 0 => [{2,12}]
  | 1 => [{0,10}]
  | 2 => [∅,{18}]
  | 3 => [∅,{17},{19},{7},{7,17},{7,19},{9},{9,17},{9,19}]
  | 4 => [∅,{3}]
  | 5 => [{4,13},{4,13,16},{4,5,13},{4,5,13,16}]
  | 6 => [{8,16},{8,18},{8,16,18},{5,8,16},{5,8,16,18}]
  | 7 => [{3,14},{5,14},{5,14,16},{3,5,14},{3,5,14,16}]
  | 8 => [{1,11},{1,3,11}]
  | 9 => [{6,15},{6,15,18}]
  | 10 => [{9,19},{9,16,19},{7,9,19}]
  | _ => [{7,17},{7,17,19},{5,7,17}]

def pruningDomain4 (i : Fin 12) : List (Finset Nat) :=
  match i.val with
  | 0 => [{2,12}]
  | 1 => [{0,10}]
  | 2 => [∅,{18}]
  | 3 => [∅]
  | 4 => [∅,{3}]
  | 5 => [{4,13},{4,13,16},{4,5,13},{4,5,13,16}]
  | 6 => [{8,16},{8,18},{8,16,18},{5,8,16},{5,8,16,18}]
  | 7 => [{3,14},{5,14},{5,14,16},{3,5,14},{3,5,14,16}]
  | 8 => [{1,11},{1,3,11}]
  | 9 => [{6,15},{6,15,18}]
  | 10 => [{9,19},{9,16,19}]
  | _ => [{7,17},{5,7,17}]


/-- Four finite arc-support pruning steps. A candidate survives whenever
it has a disjoint partner in every distinct owner's previous domain. -/
def pruningStage (s : Fin 5) (i : Fin 12) : List (Finset Nat) :=
  match s.val with
  | 0 => auxiliaryDomain i
  | 1 => pruningDomain1 i
  | 2 => pruningDomain2 i
  | 3 => pruningDomain3 i
  | _ => pruningDomain4 i

def PruningStepCheck (old next : Fin 12 → List (Finset Nat)) (i : Fin 12) : Prop :=
  ∀ m ∈ old i,
    (∀ j : Fin 12, j ≠ i → ∃ n ∈ old j, Disjoint m n) → m ∈ next i

instance (old next : Fin 12 → List (Finset Nat)) (i : Fin 12) :
    Decidable (PruningStepCheck old next i) :=
  inferInstanceAs (Decidable (∀ m ∈ old i,
    (∀ j : Fin 12, j ≠ i → ∃ n ∈ old j, Disjoint m n) → m ∈ next i))

/-- Each candidate deletion is justified by the absence of an exact finite
partner, and each owner/round is checked separately by the kernel. -/
theorem pruning_step_checked (s : Fin 4) (i : Fin 12) :
    PruningStepCheck (pruningStage ⟨s.val, by omega⟩)
      (pruningStage ⟨s.val+1, by omega⟩) i := by
  fin_cases s <;> fin_cases i <;> decide +kernel

theorem actual_pruning_step (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (old next : Fin 12 → List (Finset Nat))
    (hcheck : ∀ i, PruningStepCheck old next i)
    (hold : ∀ i, natCombinedOwners p (orderedOwner p i) ∈ old i) :
    ∀ i, natCombinedOwners p (orderedOwner p i) ∈ next i := by
  intro i
  apply hcheck i _ (hold i)
  intro j hji
  refine ⟨natCombinedOwners p (orderedOwner p j), hold j, ?_⟩
  apply nat_combined_disjoint
  intro he
  exact hji (ordered_owner_injective p hf he).symm

/-- An actual packing survives every finite pruning round, because its
actual neighbor supplies the required disjoint partner at each step. -/
theorem pruned_auxiliary_domain_actual (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∀ i, natCombinedOwners p (orderedOwner p i) ∈ pruningDomain4 i := by
  have h0 : ∀ i, natCombinedOwners p (orderedOwner p i) ∈ pruningStage 0 i :=
    auxiliary_domain_actual p hf
  have h1 := actual_pruning_step p hf _ _ (pruning_step_checked 0) h0
  have h2 := actual_pruning_step p hf _ _ (pruning_step_checked 1) h1
  have h3 := actual_pruning_step p hf _ _ (pruning_step_checked 2) h2
  exact actual_pruning_step p hf _ _ (pruning_step_checked 3) h3


def auxiliaryDomains : List (List (Finset Nat)) :=
  (List.finRange 12).map pruningDomain4

/-- Every disjoint complete vector admitted by the necessary owner domains.
    The exact finite support pruning preserves every actual packing.
    This table is computed in Lean, rather than supplied by a Python count. -/
def auxiliaryVectors : List (List (Finset Nat)) :=
  enumerateVectors auxiliaryDomains ∅


theorem auxiliary_vector_count : auxiliaryVectors.length = 57 := by
  rw [auxiliaryVectors, enumerateVectors_length]
  decide +kernel

theorem auxiliary_vectors_distinct : auxiliaryVectors.Nodup := by
  apply enumerateVectors_nodup
  intro d hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
  fin_cases i <;> decide +kernel

noncomputable def actualAuxiliaryVector (p : NormalizedPacking) : List (Finset Nat) :=
  (List.finRange 12).map fun i => natCombinedOwners p (orderedOwner p i)

theorem actual_auxiliary_slot (p : NormalizedPacking) (i : Fin 12) :
    (actualAuxiliaryVector p)[i.val]! = natCombinedOwners p (orderedOwner p i) := by
  fin_cases i <;> rfl

/-- Universal geometric coverage by the complete 57-vector table. Every
    component is the entire actual F/G ownership set of its original owner. -/
theorem actual_auxiliary_vector_mem (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    actualAuxiliaryVector p ∈ auxiliaryVectors := by
  have hmem : List.Forall₂ (fun m d => m ∈ d)
      (actualAuxiliaryVector p) auxiliaryDomains := by
    rw [actualAuxiliaryVector, auxiliaryDomains,
      List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    exact pruned_auxiliary_domain_actual p hf i
  have hindices : (List.finRange 12).Pairwise (fun i j => i ≠ j) := by decide +kernel
  have hpair : (actualAuxiliaryVector p).Pairwise Disjoint := by
    rw [actualAuxiliaryVector, List.pairwise_map]
    apply hindices.imp
    intro i j hij
    exact nat_combined_disjoint p _ _ (fun he => hij (ordered_owner_injective p hf he))
  exact actual_owners_mem_enumerateVectors _ _ ∅ hmem
    (by intros; exact Finset.disjoint_empty_right _) hpair

/-- The cover includes all original square labels through a proved
    bijection, and uses the exact sorted F followed by sorted G convention. -/
theorem auxiliary_vector_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    actualAuxiliaryVector p ∈ auxiliaryVectors ∧
      Function.Bijective (orderedOwner p) ∧
      (∀ i, markerCode p (orderedOwner p i) = auxiliaryCode i) ∧
      (∀ i, AuxExact (p.square (orderedOwner p i)) 2
        (actualAuxiliaryVector p)[i.val]!) := by
  refine ⟨actual_auxiliary_vector_mem p hf, ordered_owner_bijective p hf,
    ordered_owner_code p hf, ?_⟩
  intro i
  rw [actual_auxiliary_slot]
  exact nat_combined_exact p _

theorem retained_auxiliary_vector_cover (r : CoverRow) (hr : r ∈ retainedRows)
    (hid : r.originalId = 977) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = r.groups) :
    actualAuxiliaryVector p ∈ auxiliaryVectors ∧
      Function.Bijective (orderedOwner p) ∧
      (∀ i, markerCode p (orderedOwner p i) = auxiliaryCode i) ∧
      (∀ i, AuxExact (p.square (orderedOwner p i)) 2
        (actualAuxiliaryVector p)[i.val]!) :=
  auxiliary_vector_cover p (hf.trans (row_family r hr hid))

#print axioms auxiliary_vector_count
#print axioms auxiliary_vector_cover
end S12Completion.C977
