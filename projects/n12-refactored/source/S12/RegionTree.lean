import S12.LinearImplication

namespace S12

abbrev PlaneConstraint := LinearConstraint 2
abbrev RegionConstraints := List PlaneConstraint
abbrev FarkasTerms := List (ℚ × PlaneConstraint)

/-- A cover proof may branch on an arbitrary halfplane, close an inconsistent
linear system, or contradict a geometrically forbidden open region. -/
inductive RegionTree where
  | leaf
  | empty (terms : FarkasTerms)
  | cut (test : PlaneConstraint) (yes no : RegionTree)
  | forbidden (block : RegionConstraints) (proofs : List FarkasTerms)

def RegionTree.Check (inputs : RegionConstraints) (forbidden : List RegionConstraints) : RegionTree→Prop
  | .leaf => True
  | .empty terms => LinearCertificateCheck inputs terms
  | .cut test yes no => yes.Check (test::inputs) forbidden ∧ no.Check (test.opposite::inputs) forbidden
  | .forbidden block proofs => block∈forbidden ∧
      ∀ r∈block,∃ terms∈proofs,LinearImplicationCheck inputs r terms
instance decidableRegionTreeCheck (inputs : RegionConstraints) (forbidden : List RegionConstraints)
    (tree : RegionTree) : Decidable (tree.Check inputs forbidden) := by
  match tree with
  | .leaf => exact isTrue trivial
  | .empty terms => exact inferInstanceAs (Decidable (LinearCertificateCheck _ _))
  | .cut test yes no =>
    haveI := decidableRegionTreeCheck (test::inputs) forbidden yes
    haveI := decidableRegionTreeCheck (test.opposite::inputs) forbidden no
    exact inferInstanceAs (Decidable (_ ∧ _))
  | .forbidden block proofs => exact inferInstanceAs (Decidable (_ ∧ _))

def RegionTree.leaves (inputs : RegionConstraints) : RegionTree→List RegionConstraints
  | .leaf => [inputs]
  | .empty _ => []
  | .cut test yes no => yes.leaves (test::inputs)++no.leaves (test.opposite::inputs)
  | .forbidden _ _ => []

/-- Every real center survives into a recorded leaf unless its assumptions
are contradictory. Clipping, vertex enumeration and the search strategy
are external; this theorem checks coverage of every real center. -/
theorem RegionTree.sound (tree : RegionTree) (inputs : RegionConstraints)
    (forbidden : List RegionConstraints) (hc : tree.Check inputs forbidden)
    (x : Fin 2→ℝ) (hx : ∀ r∈inputs,r.Holds x)
    (hf : ∀ block∈forbidden,¬(∀ r∈block,r.Holds x)) :
    ∃ leaf∈tree.leaves inputs,∀ r∈leaf,r.Holds x := by
  induction tree generalizing inputs with
  | leaf => exact ⟨inputs,by simp [RegionTree.leaves],hx⟩
  | empty terms => exact False.elim (linear_certificate_sound inputs terms hc ⟨x,hx⟩)
  | cut test yes no ihy ihn =>
    by_cases ht : test.Holds x
    · obtain ⟨leaf,hl,hs⟩ := ihy _ hc.1 (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact ht; exact hx r hr)
      exact ⟨leaf,List.mem_append_left _ hl,hs⟩
    · have ht' := (LinearConstraint.opposite_holds test x).mpr ht
      obtain ⟨leaf,hl,hs⟩ := ihn _ hc.2 (by intro r hr; rcases List.mem_cons.mp hr with rfl | hr; exact ht'; exact hx r hr)
      exact ⟨leaf,List.mem_append_right _ hl,hs⟩
  | forbidden block proofs =>
    apply False.elim
    apply hf block hc.1
    intro r hr
    obtain ⟨terms,_,hterms⟩ := hc.2 r hr
    exact linear_implication_sound inputs r terms hterms x hx

#print axioms RegionTree.sound
end S12
