import Compact.Geometry.C1092WallPhysical
import S12.CoreExclusion
import S12.Convex
import S12.CornerForcing
import Compact.Geometry.ClosedPointExclusion

/-! Original C1092 ownership to four simultaneous wall barriers.
Every square remains in the same physical packing. The four local frames
only apply the uniform wall lemma. No auxiliary assignment, angle bound,
central ordering, or historical residual enclosure is assumed here.
Source-only: this module has not been replayed. -/
namespace N12Compact.C1092WallCycle
open S12 S12Pilot C1092WallPolynomial C1092WallPhysical
set_option Elab.async false

def family : Finset Nat :=
  {3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}

/-- Original owner order: four corner pairs, four central singletons,
then left, bottom, right, top singleton wall owners. -/
def ownerCode : Fin 12 → Nat :=
  ![3,12,48,192,256,512,1024,2048,4096,8192,16384,32768]

noncomputable def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerCode i))

theorem owner_code (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) : markerCode p (ownerIndex p (ownerCode i)) = ownerCode i := by
  apply ownerIndex_spec
  rw [hf]
  fin_cases i <;> decide

theorem owners_markers (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) : ExactMarkers (owners p i) (maskSupport (ownerCode i)) := by
  simpa only [owners,owner_code p hf i] using coded_exact p (ownerIndex p (ownerCode i))

theorem owners_disjoint (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (hij : i ≠ j) (x y : ℝ) :
    ¬ ((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro h
  have hc : ownerCode i = ownerCode j :=
    (owner_code p hf i).symm.trans ((congrArg (markerCode p) h).trans (owner_code p hf j))
  have injective : Function.Injective ownerCode := by decide
  exact hij (injective hc)

def wallOwner : Fin 4 → Fin 12 := ![8,9,10,11]
def centralOwner : Fin 4 → Fin 12 := ![4,5,6,7]
def cornerOwner : Fin 4 → Fin 12 := ![0,1,2,3]
def cornerPoint : Fin 4 → ℚ × ℚ := ![(1,1),(3,1),(3,3),(1,3)]

theorem corner_points (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 4) : (owners p (cornerOwner k)).Inside
      (cornerPoint k).1 (cornerPoint k).2 := by
  apply seed_points_sound _
    (by change 1 < (p.square _).side; rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square _).side ≤ 1001/1000; rw [p.congruent]; exact p.side_le)
    (p.contained _) _ (owners_markers p hf (cornerOwner k))
  have finite : ∀ k : Fin 4,
      cornerPoint k ∈ seedPoints (maskSupport (ownerCode (cornerOwner k))) := by decide +kernel
  exact finite k

noncomputable def localFrame (k : Fin 4) (q : OpenSquare) : OpenSquare :=
  ![q,pullSwap q,pullX q,pullX (pullSwap q)] k

noncomputable def wallFrame (p : NormalizedPacking) (k : Fin 4) : OpenSquare :=
  localFrame k (owners p (wallOwner k))

def pointMap (k : Fin 4) (x y : ℝ) : ℝ × ℝ :=
  ![(x,y),(y,x),(4-x,y),(y,4-x)] k

def markerMap (k : Fin 4) (j : Marker) : Marker :=
  ![j,permSwap j,permX j,permSwap (permX j)] k

theorem local_inside (k : Fin 4) (q : OpenSquare) (x y : ℝ) :
    (localFrame k q).Inside x y ↔ q.Inside (pointMap k x y).1 (pointMap k x y).2 := by
  fin_cases k <;> simp [localFrame,pointMap,inside_pullX,inside_pullSwap]

private theorem local_owns (k : Fin 4) (q : OpenSquare) (j : Marker) :
    Owns (localFrame k q) j ↔ Owns q (markerMap k j) := by
  fin_cases k <;> simp [localFrame,markerMap,owns_pullX,owns_pullSwap]

private theorem frame_side (p : NormalizedPacking) (k : Fin 4) :
    (wallFrame p k).side = p.commonSide := by
  have hs : (wallFrame p k).side = (owners p (wallOwner k)).side := by
    fin_cases k <;> rfl
  rw [hs]
  exact p.congruent _

private theorem frame_box (p : NormalizedPacking) (k : Fin 4) :
    InsideContainer (wallFrame p k) := by
  fin_cases k
  · exact p.contained _
  · exact container_pullSwap _ (p.contained _)
  · exact container_pullX _ (p.contained _)
  · exact container_pullX _ (container_pullSwap _ (p.contained _))

/-- Each actual wall owner owns exactly marker12 in its local chart. -/
theorem frame_singleton (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 4) (j : Marker) : Owns (wallFrame p k) j ↔ j = 12 := by
  change Owns (localFrame k (owners p (wallOwner k))) j ↔ j = 12
  rw [local_owns,owners_markers p hf (wallOwner k) (markerMap k j)]
  have finite : ∀ k : Fin 4, ∀ j : Marker,
      markerMap k j ∈ maskSupport (ownerCode (wallOwner k)) ↔ j = 12 := by decide
  exact finite k j

abbrev WallBranch := Fin 4 → Bool

noncomputable def branchY (b : Bool) (y : ℝ) : ℝ := if b then y else 4-y

noncomputable def forcedPoint (k : Fin 4) (b : Bool) (i : Fin 12) : ℝ × ℝ :=
  pointMap k (targetX i) (branchY b (targetY i))

def WallContext (p : NormalizedPacking) (b : WallBranch) : Prop :=
  ∀ k : Fin 4,
    (if b k then centerY (wallFrame p k) ≤ 2 else 2 ≤ centerY (wallFrame p k)) ∧
    ∀ i : Fin 12, (owners p (wallOwner k)).Inside
      (forcedPoint k (b k) i).1 (forcedPoint k (b k) i).2

/-- Every original packing supplies one simultaneous 16-sign wall context.
No assignment enumeration and no change to the original packing is needed. -/
theorem original_wall_context (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : ∃ b : WallBranch, WallContext p b := by
  classical
  have each : ∀ k : Fin 4, ∃ b : Bool,
      (if b then centerY (wallFrame p k) ≤ 2 else 2 ≤ centerY (wallFrame p k)) ∧
      ∀ i : Fin 12, (owners p (wallOwner k)).Inside
        (forcedPoint k b i).1 (forcedPoint k b i).2 := by
    intro k
    have h := singleton_wall_point_cover (wallFrame p k)
      (by rw [frame_side]; exact p.side_gt_one)
      (by rw [frame_side]; exact p.side_le) (frame_box p k)
      ((frame_singleton p hf k 12).mpr rfl)
      (fun j hj h => hj ((frame_singleton p hf k j).mp h))
    rcases h with ⟨hy,hpoints⟩ | ⟨hy,hpoints⟩
    · refine ⟨true,hy,?_⟩
      intro i
      exact (local_inside k _ _ _).mp (hpoints i)
    · refine ⟨false,hy,?_⟩
      intro i
      exact (local_inside k _ _ _).mp (hpoints i)
  choose b hb using each
  exact ⟨b,hb⟩

/-- All 48 compulsory points are foreign to each of the four central
owners. The original disjointness is the entire transfer argument. -/
theorem central_missing_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (j k : Fin 4) (i : Fin 12) :
    ¬ (owners p (centralOwner j)).Inside
      (forcedPoint k (b k) i).1 (forcedPoint k (b k) i).2 := by
  intro h
  have different : ∀ j k : Fin 4, centralOwner j ≠ wallOwner k := by decide
  exact owners_disjoint p hf _ _ (different j k) _ _ ⟨h,(hb k).2 i⟩

/-- The two endpoints at x=1 contain the exact old F-point y=87/50.
This interpolation is strict, including the closed segment endpoints. -/
theorem local_wall_segment (p : NormalizedPacking) (b : WallBranch)
    (hb : WallContext p b) (k : Fin 4) (y : ℝ)
    (hy0 : 803/500 ≤ y) (hy1 : y ≤ 947/500) :
    (owners p (wallOwner k)).Inside
      (pointMap k 1 (branchY (b k) y)).1
      (pointMap k 1 (branchY (b k) y)).2 := by
  have low := (local_inside k _ _ _).mpr ((hb k).2 10)
  have high := (local_inside k _ _ _).mpr ((hb k).2 11)
  change (wallFrame p k).Inside (targetX 10) (branchY (b k) (targetY 10)) at low
  change (wallFrame p k).Inside (targetX 11) (branchY (b k) (targetY 11)) at high
  norm_num [targetX,targetY] at low high
  let t : ℝ := (y-803/500)/(36/125)
  have ht0 : 0 ≤ t := by dsimp [t]; nlinarith only [hy0]
  have ht1 : t ≤ 1 := by dsimp [t]; nlinarith only [hy1]
  have h := inside_segment (wallFrame p k) 1 _ 1 _ t low high ht0 ht1
  apply (local_inside k _ _ _).mp
  convert h using 1
  · ring
  · cases hbk : b k <;> simp [branchY,hbk,t] <;> ring

theorem wall_auxiliary_point (p : NormalizedPacking) (b : WallBranch)
    (hb : WallContext p b) (k : Fin 4) :
    (owners p (wallOwner k)).Inside
      (pointMap k 1 (branchY (b k) (87/50))).1
      (pointMap k 1 (branchY (b k) (87/50))).2 :=
  local_wall_segment p b hb k (87/50) (by norm_num) (by norm_num)

/-- The central owner cannot reclaim even a single point of the entire
occupied wall segment; this is stronger than a finite foreign-point list. -/
theorem central_missing_segment (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (j k : Fin 4) (y : ℝ) (hy0 : 803/500 ≤ y) (hy1 : y ≤ 947/500) :
    ¬ (owners p (centralOwner j)).Inside
      (pointMap k 1 (branchY (b k) y)).1
      (pointMap k 1 (branchY (b k) y)).2 := by
  intro h
  have different : ∀ j k : Fin 4, centralOwner j ≠ wallOwner k := by decide
  exact owners_disjoint p hf _ _ (different j k) _ _
    ⟨h,local_wall_segment p b hb k y hy0 hy1⟩

/-- Strict ownership by the wall rules out even closed membership in a
central square. This keeps the true boundary-contact implication explicit. -/
theorem central_missing_closed_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (j k : Fin 4) (i : Fin 12) :
    ¬ FourSquareAnchors.ClosedInside (owners p (centralOwner j))
      (forcedPoint k (b k) i).1 (forcedPoint k (b k) i).2 := by
  intro h
  have different : ∀ j k : Fin 4, wallOwner k ≠ centralOwner j := by decide
  exact ClosedPointExclusion.outside_of_closed _ _ _ _
    (owners_disjoint p hf _ _ (different j k)) h ((hb k).2 i)

theorem central_missing_closed_corners (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (j k : Fin 4) :
    ¬ FourSquareAnchors.ClosedInside (owners p (centralOwner j))
      (cornerPoint k).1 (cornerPoint k).2 := by
  intro h
  have different : ∀ j k : Fin 4, cornerOwner k ≠ centralOwner j := by decide
  exact ClosedPointExclusion.outside_of_closed _ _ _ _
    (owners_disjoint p hf _ _ (different j k)) h (corner_points p hf k)

/-- Honest remaining family interface. The finisher retains the complete
twelve-square packing; replacing it by the point-only central relaxation
is unsound, as the separate eight-square countermodel demonstrates. -/
theorem excludes_family_of_wall_context
    (finish : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
      ∀ b : WallBranch, WallContext p b → False) :
    ∀ p : NormalizedPacking, codedMarkerFamily p = family → False := by
  intro p hf
  obtain ⟨b,hb⟩ := original_wall_context p hf
  exact finish p hf b hb

#print axioms original_wall_context
#print axioms central_missing_segment
end N12Compact.C1092WallCycle
