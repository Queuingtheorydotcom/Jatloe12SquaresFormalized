import Compact.Completion.FiniteCases.TransposeOwnerDomain
import Compact.Completion.CommonCases.OriginalOwners

/-! Original G ownership for C580 and C581. Ten ordinary owners consume
the ten G points. The complete actual sets are derived from local checked
domains and disjointness, without importing the paper's final label list. -/
namespace N12Compact.FiniteCases.C580581Entrance
open S12 S12Pilot RelaxedOwnerDomain
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

def bottomMask : Fin 2 → Nat := ![8192,8196]
def family : Fin 2 → Finset Nat :=
  ![{1,2,8,48,192,512,1024,2304,4096,8192,16384,32768},
    {1,2,8,48,192,512,1024,2304,4096,8196,16384,32768}]

private def swG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 1 1 :=
  ofSingle _ singleSpec2 singleSpec2_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def lowG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 2 1 :=
  ofSingle _ singleSpec6 singleSpec6_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def seG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 8 1 :=
  TransposeOwnerDomain.transported _ 8 singleSpec6 singleSpec6_checked
    ⟨false,true,false⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    1 1 (by decide +kernel) reflectXG reflectXG_points
    (by fin_cases v <;> decide +kernel)
private def mergedG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 2304 1 :=
  TransposeOwnerDomain.transported _ 2304 singleSpec33 singleSpec33_checked
    ⟨true,false,false⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    0 1 (by decide +kernel) TransposeOwnerDomain.swapFG
    TransposeOwnerDomain.swapFG_points (by fin_cases v <;> decide +kernel)
private def bottomG (v : Fin 2) :
    OwnerBudget.HalfDomain (family v) (bottomMask v) 1 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.elim0 j) i) v
  · exact ofSingle _ singleSpec68 singleSpec68_checked 1 (by decide +kernel)
      (by decide +kernel)
  · exact OwnerBudget.HalfDomain.ofSeedHull _ 8196 1 5 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def leftG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 4096 1 :=
  ofSingle _ singleSpec57 singleSpec57_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def southG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 512 1 :=
  ofSingle _ singleSpec27 singleSpec27_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def rightG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 16384 1 :=
  ofSingle _ singleSpec77 singleSpec77_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def northG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 1024 1 :=
  ofSingle _ singleSpec35 singleSpec35_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)
private def topG (v : Fin 2) : OwnerBudget.HalfDomain (family v) 32768 1 :=
  ofSingle _ singleSpec90 singleSpec90_checked 1 (by decide +kernel)
    (by fin_cases v <;> decide +kernel)

def G (p : NormalizedPacking) (mask : Nat) : Finset Nat :=
  natAuxOwners p 1 (ownerIndex p mask)

private theorem actual (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (mask : Nat) (member : mask∈family v)
    (d : OwnerBudget.HalfDomain (family v) mask 1) : G p mask∈d.allowed :=
  d.sound p _ hf (code _ p hf mask member)

private theorem separate (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (m n : Nat)
    (hm : m∈family v) (hn : n∈family v) (different : m≠n) :
    Disjoint (G p m) (G p n) := by
  apply nat_aux_disjoint
  intro same
  exact different ((code _ p hf m hm).symm.trans
    ((congrArg (markerCode p) same).trans (code _ p hf n hn)))

private theorem absent (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (m n : Nat)
    (hm : m∈family v) (hn : n∈family v) (different : m≠n)
    (index : Nat) (owned : G p n={index}) : index∉G p m := by
  intro member
  exact Finset.disjoint_left.mp (separate v p hf m n hm hn different)
    member (by rw [owned]; exact Finset.mem_singleton_self index)

def claims (v : Fin 2) : Fin 10 → Nat×Nat :=
  ![(1,2),(2,0),(8,8),(2304,3),(bottomMask v,5),(4096,1),
    (512,6),(16384,9),(1024,7),(32768,4)]

/-- Full original G sets, including the auxiliary point of the genuine
merged left-central owner. Both original families are included. -/
theorem forced (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (i : Fin 10) :
    G p (claims v i).1={(claims v i).2} := by
  have members (m : Nat) (checked : ∀ v : Fin 2, m∈family v) : m∈family v := checked v
  have sw : G p 1={2} := by
    have h := actual v p hf 1 (by fin_cases v <;> decide +kernel) (swG v)
    simpa only [swG,ofSingle,singleSpec2,List.mem_singleton] using h
  have low : G p 2={0} := by
    have h := actual v p hf 2 (by fin_cases v <;> decide +kernel) (lowG v)
    simpa only [lowG,ofSingle,singleSpec6,List.mem_singleton] using h
  have se : G p 8={8} := by
    have h := actual v p hf 8 (by fin_cases v <;> decide +kernel) (seG v)
    have exactList : (seG v).allowed=[{8}] := by fin_cases v <;> decide +kernel
    simpa only [exactList,List.mem_singleton] using h
  have merged : G p 2304={3} := by
    have h := actual v p hf 2304 (by fin_cases v <;> decide +kernel) (mergedG v)
    have exactList : (mergedG v).allowed=[{3}] := by fin_cases v <;> decide +kernel
    simpa only [exactList,List.mem_singleton] using h
  have bottom : G p (bottomMask v)={5} := by
    have h := actual v p hf (bottomMask v) (by fin_cases v <;> decide +kernel) (bottomG v)
    have opts : ∀ v : Fin 2, (bottomG v).allowed ⊆ ([{2},{5}] : List (Finset Nat)) := by
      intro v; fin_cases v <;> decide +kernel
    have choices := opts v h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at choices
    rcases choices with bad | good
    · have missing := absent v p hf (bottomMask v) 1
        (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) 2 sw
      exact False.elim (missing (by rw [bad]; decide +kernel))
    · exact good
  have left : G p 4096={1} := by
    have h := actual v p hf 4096 (by fin_cases v <;> decide +kernel) (leftG v)
    change G p 4096∈([{0},{1},{3}] : List (Finset Nat)) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have no0 := absent v p hf 4096 2 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 0 low
    have no3 := absent v p hf 4096 2304 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 3 merged
    rcases h with bad | good | bad
    · exact False.elim (no0 (by rw [bad]; decide +kernel))
    · exact good
    · exact False.elim (no3 (by rw [bad]; decide +kernel))
  have south : G p 512={6} := by
    have h := actual v p hf 512 (by fin_cases v <;> decide +kernel) (southG v)
    change G p 512∈([{5},{6},{8}] : List (Finset Nat)) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have no5 := absent v p hf 512 (bottomMask v) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel) 5 bottom
    have no8 := absent v p hf 512 8 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 8 se
    rcases h with bad | good | bad
    · exact False.elim (no5 (by rw [bad]; decide +kernel))
    · exact good
    · exact False.elim (no8 (by rw [bad]; decide +kernel))
  have right : G p 16384={9} := by
    have h := actual v p hf 16384 (by fin_cases v <;> decide +kernel) (rightG v)
    change G p 16384∈([{6},{8},{9}] : List (Finset Nat)) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have no6 := absent v p hf 16384 512 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 6 south
    have no8 := absent v p hf 16384 8 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 8 se
    rcases h with bad | bad | good
    · exact False.elim (no6 (by rw [bad]; decide +kernel))
    · exact False.elim (no8 (by rw [bad]; decide +kernel))
    · exact good
  have north : G p 1024={7} := by
    have h := actual v p hf 1024 (by fin_cases v <;> decide +kernel) (northG v)
    change G p 1024∈([{6},{7},{9}] : List (Finset Nat)) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    have no6 := absent v p hf 1024 512 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 6 south
    have no9 := absent v p hf 1024 16384 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) 9 right
    rcases h with bad | good | bad
    · exact False.elim (no6 (by rw [bad]; decide +kernel))
    · exact good
    · exact False.elim (no9 (by rw [bad]; decide +kernel))
  have top : G p 32768={4} := by
    have h := actual v p hf 32768 (by fin_cases v <;> decide +kernel) (topG v)
    change G p 32768∈([{4},{7}] : List (Finset Nat)) at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with good | bad
    · exact good
    · have no7 := absent v p hf 32768 1024 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) 7 north
      exact False.elim (no7 (by rw [bad]; decide +kernel))
  fin_cases i <;> simp only [claims] <;>
    first | exact sw | exact low | exact se | exact merged | exact bottom |
      exact left | exact south | exact right | exact north | exact top

theorem inside (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (i : Fin 10) :
    (owner p (claims v i).1).Inside
      ((auxPoints 1)[(claims v i).2]!).1 ((auxPoints 1)[(claims v i).2]!).2 := by
  apply (nat_aux_exact p 1 (ownerIndex p (claims v i).1) (claims v i).2
    (by fin_cases v <;> fin_cases i <;> decide +kernel)).mpr
  change (claims v i).2∈G p (claims v i).1
  rw [forced v p hf i]
  exact Finset.mem_singleton_self _

#print axioms forced
#print axioms inside
end
end N12Compact.FiniteCases.C580581Entrance
