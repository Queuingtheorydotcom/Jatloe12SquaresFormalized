import Compact.Bridge.RelaxedOwnerDomain
import S12.Seeds
import S12.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace N12Compact.CommonCases.OriginalOwners
open S12 S12Pilot
set_option Elab.async false

noncomputable def owner (p : NormalizedPacking) (mask : Nat) : OpenSquare :=
  p.square (ownerIndex p mask)

noncomputable def auxiliaries (p : NormalizedPacking) (mask : Nat) : Finset Nat :=
  natCombinedOwners p (ownerIndex p mask)

theorem code (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (hm : mask∈family) :
    markerCode p (ownerIndex p mask)=mask := ownerIndex_spec p mask (by rw [hf]; exact hm)

theorem side (p : NormalizedPacking) (mask : Nat) : 1 < (owner p mask).side := by
  change 1 < (p.square (ownerIndex p mask)).side
  rw [p.congruent]
  exact p.side_gt_one

theorem box (p : NormalizedPacking) (mask : Nat) : InsideContainer (owner p mask) :=
  p.contained _

theorem seed (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (hm : mask∈family)
    (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport mask)) :
    (owner p mask).Inside P.1 P.2 := by
  have hc := code family p hf mask hm
  exact seed_points_sound (p.square (ownerIndex p mask)) (side p mask)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    (maskSupport mask) (by simpa only [owner,hc] using coded_exact p (ownerIndex p mask))
    P checked

/-- Preserve an original marker exclusion from the owner's exact signature.
This makes no assertion that the marker has an owner elsewhere. -/
theorem missing_marker (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (hm : mask∈family)
    (m : Marker) (absent : m∉maskSupport mask) :
    ¬(owner p mask).Inside (marker m).1 (marker m).2 := by
  have hc := code family p hf mask hm
  have exactMarkers : ExactMarkers (owner p mask) (maskSupport mask) := by
    simpa only [owner,hc] using coded_exact p (ownerIndex p mask)
  intro own
  exact absent ((exactMarkers m).mp own)

theorem apart (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (m n : Nat)
    (hm : m∈family) (hn : n∈family) (different : m≠n) :
    ∀ x y, ¬ ((owner p m).Inside x y ∧ (owner p n).Inside x y) := by
  apply p.disjoint
  intro same
  exact different ((code family p hf m hm).symm.trans
    ((congrArg (markerCode p) same).trans (code family p hf n hn)))

theorem auxiliary_disjoint (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (m n : Nat)
    (hm : m∈family) (hn : n∈family) (different : m≠n) :
    Disjoint (auxiliaries p m) (auxiliaries p n) := by
  apply nat_combined_disjoint
  intro same
  exact different ((code family p hf m hm).symm.trans
    ((congrArg (markerCode p) same).trans (code family p hf n hn)))

theorem auxiliary_exact (p : NormalizedPacking) (mask index : Nat) (bound : index<20) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 ↔
      index∈auxiliaries p mask :=
  nat_combined_exact p (ownerIndex p mask) index
    (by change index∈List.range 20; exact List.mem_range.mpr bound)

theorem domain (family : Finset Nat) (d : CertifiedDomain family) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : d.mask∈family) :
    auxiliaries p d.mask ∈ d.allowed :=
  d.sound p (ownerIndex p d.mask) hf (code family p hf d.mask member)

/-- Cache the literal fields after an authentic domain construction. The
soundness proof retains that construction; finite cuts only reduce the
explicit owner list. -/
noncomputable def cached_domain (family : Finset Nat) (d : CertifiedDomain family)
    (mask : Nat) (allowed : List (Finset Nat)) (hm : d.mask=mask)
    (ha : d.allowed=allowed) : CertifiedDomain family :=
  ⟨mask,allowed,by
    intro p i hf hi
    rw [←ha]
    exact d.sound p i hf (hi.trans hm.symm)⟩

/-- For an ordinary owner under the actual F3/G2 budget, filter only the
two small cardinalities. The large exemption table is checked once in the
inputs instead of re-evaluated for every allowed label. -/
noncomputable def restrict_budget23 (family : Finset Nat) (d : CertifiedDomain family)
    (fcount : (family∩auxExempt 0).card=3) (gcount : (family∩auxExempt 1).card=2)
    (fNon : d.mask∉auxExempt 0) (gNon : d.mask∉auxExempt 1) : CertifiedDomain family :=
  ⟨d.mask,d.allowed.filter (fun owned => decide
    ((RelaxedOwnerDomain.firstHalf owned).card≤2 ∧
      (RelaxedOwnerDomain.secondHalf owned).card=1)),by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi,decide_eq_true ?_⟩
    have hF := nat_aux_budget p 0 i
    have hG := nat_aux_budget p 1 i
    rw [hf,hi,fcount] at hF
    rw [hf,hi,gcount] at hG
    simp only [fNon,gNon,ite_false] at hF hG
    unfold natCombinedOwners
    rw [RelaxedOwnerDomain.firstHalf_combined _ _ (nat_aux_subset p 0 i),
      RelaxedOwnerDomain.secondHalf_combined _ _ (nat_aux_subset p 0 i),
      Finset.card_image_of_injective _ (show Function.Injective (fun n : Nat => n+10) by
        intro a b h
        exact Nat.add_right_cancel h)]
    exact ⟨hF.2,le_antisymm hG.2 hG.1⟩⟩

theorem known_point (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (mask : Nat) (member : mask∈family)
    (owned : Finset Nat) (equal : auxiliaries p mask=owned)
    (P : ℚ×ℚ) (checked : P∈queryInsidePoints mask 2 owned) :
    (owner p mask).Inside P.1 P.2 := by
  have hc := code family p hf mask member
  have hExact := nat_combined_exact p (ownerIndex p mask)
  change AuxExact (owner p mask) 2 (auxiliaries p mask) at hExact
  rw [equal] at hExact
  exact query_inside_sound mask 2 owned (owner p mask) (side p mask)
    (by change (p.square (ownerIndex p mask)).side ≤ 1001/1000
        rw [p.congruent]; exact p.side_le) (box p mask)
    (by simpa only [owner,hc] using coded_exact p (ownerIndex p mask)) hExact P checked

theorem horizontal_segment (q : OpenSquare) (x0 x1 y x : ℝ)
    (a : q.Inside x0 y) (b : q.Inside x1 y) (ordered : x0<x1)
    (low : x0≤x) (high : x≤x1) : q.Inside x y := by
  let w := (x-x0)/(x1-x0)
  have gap : 0 < x1-x0 := sub_pos.mpr ordered
  have wn : 0 ≤ w := div_nonneg (sub_nonneg.mpr low) gap.le
  have wu : w ≤ 1 := (div_le_one gap).mpr (by linarith only [high])
  have h := inside_segment q x0 y x1 y w a b wn wu
  have hx : (1-w)*x0+w*x1=x := by
    dsimp [w]
    field_simp [ne_of_gt gap]
    <;> ring
  have hy : (1-w)*y+w*y=y := by ring
  simpa only [hx,hy] using h

theorem vertical_segment (q : OpenSquare) (x y0 y1 y : ℝ)
    (a : q.Inside x y0) (b : q.Inside x y1) (ordered : y0<y1)
    (low : y0≤y) (high : y≤y1) : q.Inside x y := by
  have h := horizontal_segment (pullSwap q) y0 y1 x y
    (by simpa only [inside_pullSwap] using a) (by simpa only [inside_pullSwap] using b)
    ordered low high
  simpa only [inside_pullSwap] using h

end N12Compact.CommonCases.OriginalOwners
