import Compact.Completion.CommonCases.C702OwnedPoints
import Compact.Completion.CommonCases.C702SouthPoint
import Compact.Completion.CommonCases.C702NorthPoint
import Compact.Completion.C981.Crosspoint
import Compact.Completion.C981.WallAdvance
import Compact.Assembly.RowIdentity

/-! Complete original C702: the merged square's genuine upper auxiliary
is forced first, then the actual SW and NW owners share one strict point. -/
namespace N12Compact.CommonCases.C702
open S12 S12Pilot S12Completion OriginalOwners
noncomputable section
set_option Elab.async false

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  have points := owned_points p hf
  have markA : (owner p 256).Inside (33/20) (33/20) := by
    have h := seed_point p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW0 : (owner p 1536).Inside (47/20) (33/20) := by
    have h := seed_point p hf 1536 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW1 : (owner p 1536).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1536 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markN : (owner p 6144).Inside (33/20) (47/20) := by
    have h := seed_point p hf 6144 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markNWall : (owner p 6144).Inside (457/500) 2 := by
    have h := seed_point p hf 6144 (by decide +kernel) (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have markT : (owner p 32768).Inside 2 (1543/500) := by
    have h := seed_point p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have cornerK : (owner p 192).Inside 1 3 := by
    have h := seed_point p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
    norm_num at h; exact h
  have topSeed : (owner p 16).Inside (213/100) (81/25) := by
    have h := seed_point p hf 16 (by decide +kernel) (213/100,81/25) (by decide +kernel)
    norm_num at h; exact h
  have leftSeed : (owner p 2).Inside (19/25) (187/100) := by
    have h := seed_point p hf 2 (by decide +kernel) (19/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun own => apart family p hf m n hm hn different _ _ ⟨own,point⟩
  have missingN := foreign 256 6144 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markN
  have missingW := foreign 256 1536 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markW0
  have missingV16 := foreign 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.leftSingleton (8/5) (by norm_num) (by norm_num))
  have missingV15 := foreign 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.leftSingleton (3/2) (by norm_num) (by norm_num))
  have missingO16 := foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.bottomSingleton (8/5) (by norm_num) (by norm_num))
  have missingO15 := foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.bottomSingleton (3/2) (by norm_num) (by norm_num))
  have southBottom : (owner p 256).Inside 2 (3/2) := by
    have h := C981CompletionCrosspoint.point (pullY (pullX (owner p 256))) (side p 256)
      (by norm_num [inside_pullX,inside_pullY]; exact points.southInward)
      (by norm_num [inside_pullX,inside_pullY]; exact points.southElbow)
      (by norm_num [inside_pullX,inside_pullY]; exact markA)
      (by norm_num [inside_pullX,inside_pullY]; exact missingN)
      (by norm_num [inside_pullX,inside_pullY]; exact missingW)
      (by norm_num [inside_pullX,inside_pullY]; exact missingV16)
      (by norm_num [inside_pullX,inside_pullY]; exact missingV15)
    norm_num [inside_pullX,inside_pullY] at h
    exact h
  have southLeft : (owner p 256).Inside (3/2) 2 := by
    let t : Transform := ⟨true,true,true⟩
    have h := C981CompletionCrosspoint.point (t.pull (owner p 256)) (side p 256)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact points.southElbow)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact points.southInward)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact markA)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingW)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingN)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingO16)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingO15)
    norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at h
    exact h
  have missingWLeft0 := foreign 1536 32 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.rightSingleton (47/20) (by norm_num) (by norm_num))
  have missingWBottom0 := foreign 1536 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.topSingleton (113/50) le_rfl (by norm_num))
  have missingWBottom1 := foreign 1536 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.topSingleton (47/20) (by norm_num) (by norm_num))
  have missingWLeft1 := foreign 1536 32 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.rightSingleton (113/50) le_rfl (by norm_num))
  have mergedNear : (owner p 1536).Inside (41/20) (41/20) := by
    have h := SouthwestPoint.point (pullY (pullX (owner p 1536))) (side p 1536)
      (by norm_num [inside_pullX,inside_pullY]; exact markW1)
      (by norm_num [inside_pullX,inside_pullY]; exact points.mergedInward)
      (by norm_num [inside_pullX,inside_pullY]; exact points.mergedElbow)
      (by norm_num [inside_pullX,inside_pullY]; exact missingWLeft0)
      (by norm_num [inside_pullX,inside_pullY]; exact missingWBottom0)
      (by norm_num [inside_pullX,inside_pullY]; exact missingWBottom1)
      (by norm_num [inside_pullX,inside_pullY]; exact missingWLeft1)
    norm_num [inside_pullX,inside_pullY] at h
    exact h
  have missingTPoint := foreign 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (points.topSingleton (113/50) le_rfl (by norm_num))
  have missingTSeed := foreign 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ topSeed
  have missingTN := foreign 32768 6144 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markN
  have topAdvance : (owner p 32768).Inside (6/5) 3 := by
    let t : Transform := ⟨true,true,true⟩
    have h := C981CompletionWallAdvance.point (t.pull (owner p 32768)) (side p 32768)
      (container_transform t _ (box p 32768))
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact markT)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact points.topLeft)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingTPoint)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingTSeed)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact missingTN)
    norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at h
    exact h
  have southPoint := C702SouthPoint.point (owner p 256) (side p 256) markA
    points.southInward points.southElbow southLeft southBottom
    (foreign 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (points.leftSingleton (33/20) (by norm_num) (by norm_num)))
    (foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (points.bottomSingleton (33/20) (by norm_num) (by norm_num))) missingN missingW
    (by
      intro w wn wu own
      exact foreign 256 1536 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (inside_segment (owner p 1536) (41/20) (41/20) (47/20) (33/20) w mergedNear markW0 wn wu) own)
  have northPoint := C702NorthPoint.point_original (owner p 6144) (side p 6144)
    markNWall markN points.northInward
    (foreign 6144 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ southLeft)
    (foreign 6144 192 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ cornerK)
    (by
      intro x lo hi own
      exact foreign 6144 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (horizontal_segment _ _ _ _ _ topAdvance points.topElbow (by norm_num) lo hi) own)
    (by
      intro w wn wu own
      exact foreign 6144 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (inside_segment (owner p 2) (19/25) (187/100) 1 (87/50) w leftSeed
          (points.leftSingleton (87/50) (by norm_num) le_rfl) wn wu)
        (by simpa only [mul_one] using own))
  exact apart family p hf 256 6144 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ _ ⟨southPoint,northPoint⟩

private theorem row_checked :
    (RowIdentity.rowAt 383).originalId=702 ∧ (RowIdentity.rowAt 383).groups=family := by decide +kernel
theorem excludes : ExcludesCase 702 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 383 702 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end
end N12Compact.CommonCases.C702
