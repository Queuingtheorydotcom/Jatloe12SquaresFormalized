import Compact.Bridge.CongruentSAT
import Compact.Geometry.ThreeSquareSupport

/-! Two actual compulsory triangles rule out both longitudinal separating
axes. The remaining alternatives are explicit transverse face inequalities.
Strict ownership of B's top marker is retained at A's axis endpoint. -/
namespace N12Compact.ABTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge S12Completion.C977

noncomputable def upper (q : OpenSquare) (nx ny : ℝ) : ℝ :=
  nx * centerX q + ny * centerY q + supportRadius q nx ny

noncomputable def lower (q : OpenSquare) (nx ny : ℝ) : ℝ :=
  nx * centerX q + ny * centerY q - supportRadius q nx ny

theorem closed_bounds (q : OpenSquare) (x y nx ny : ℝ)
    (h : ClosedInside q x y) :
    lower q nx ny ≤ nx*x+ny*y ∧ nx*x+ny*y ≤ upper q nx ny := by
  have h' := abs_le.mp (closed_support q x y nx ny h)
  constructor <;> dsimp [lower,upper] <;> linarith only [h'.1,h'.2]

theorem strict_bounds (q : OpenSquare) (x y nx ny : ℝ)
    (hn : nx^2+ny^2=1) (h : q.Inside x y) :
    lower q nx ny < nx*x+ny*y ∧ nx*x+ny*y < upper q nx ny := by
  let u := q.c*(x-centerX q)+q.s*(y-centerY q)
  let v := -q.s*(x-centerX q)+q.c*(y-centerY q)
  let A := nx*q.c+ny*q.s
  let B := -nx*q.s+ny*q.c
  have hq := (inside_centered_iff q x y).mp h
  have hu : |u| < q.side/2 := abs_lt.mpr ⟨by linarith only [hq.1],
    by linarith only [hq.2.1]⟩
  have hv : |v| < q.side/2 := abs_lt.mpr ⟨by linarith only [hq.2.2.1],
    by linarith only [hq.2.2.2]⟩
  have unit : A^2+B^2=1 := by
    calc
      _ = (nx^2+ny^2)*(q.c^2+q.s^2) := by dsimp [A,B]; ring
      _ = 1 := by rw [hn,q.unit_normal]; norm_num
  have weighted : |A| * |u| + |B| * |v| < (|A|+|B|)*(q.side/2) := by
    by_cases zero : A=0
    · have nonzero : B≠0 := by intro z; rw [zero,z] at unit; norm_num at unit
      have bound := mul_lt_mul_of_pos_left hv (abs_pos.mpr nonzero)
      simpa only [zero,abs_zero,zero_mul,zero_add] using bound
    · have first := mul_lt_mul_of_pos_left hu (abs_pos.mpr zero)
      have second := mul_le_mul_of_nonneg_left hv.le (abs_nonneg B)
      nlinarith only [first,second]
  have identity : nx*(x-centerX q)+ny*(y-centerY q)=A*u+B*v := by
    calc
      _ = (q.c^2+q.s^2)*(nx*(x-centerX q)+ny*(y-centerY q)) := by
        rw [q.unit_normal,one_mul]
      _ = _ := by dsimp [A,B,u,v]; ring
  have bound : |nx*(x-centerX q)+ny*(y-centerY q)| < supportRadius q nx ny := by
    rw [identity]
    have triangle := abs_add (A*u) (B*v)
    rw [abs_mul,abs_mul] at triangle
    dsimp [supportRadius]
    dsimp [A,B] at weighted
    nlinarith only [triangle,weighted]
  have pair := abs_lt.mp bound
  constructor <;> dsimp [lower,upper] <;> linarith only [pair.1,pair.2]

theorem ownU (q : OpenSquare) :
    lower q q.c q.s=q.loU ∧ upper q q.c q.s=q.loU+q.side := by
  have center := (center_coordinates q).1
  have radius : supportRadius q q.c q.s=q.side/2 := by
    unfold supportRadius
    rw [show q.c*q.c+q.s*q.s=1 by nlinarith only [q.unit_normal],
      show -q.c*q.s+q.s*q.c=0 by ring]
    norm_num
  constructor <;> dsimp [lower,upper] <;> rw [radius] <;> linarith only [center]

theorem ownV (q : OpenSquare) :
    lower q (-q.s) q.c=q.loV ∧ upper q (-q.s) q.c=q.loV+q.side := by
  have center := (center_coordinates q).2
  have radius : supportRadius q (-q.s) q.c=q.side/2 := by
    unfold supportRadius
    rw [show -q.s*q.c+q.c*q.s=0 by ring,
      show -(-q.s)*q.s+q.c*q.c=1 by nlinarith only [q.unit_normal]]
    norm_num
  constructor <;> dsimp [lower,upper] <;> rw [radius] <;> linarith only [center]

theorem separated (q r : OpenSquare) (nx ny : ℝ)
    (h : supportRadius q nx ny+supportRadius r nx ny ≤
      |nx*(centerX r-centerX q)+ny*(centerY r-centerY q)|) :
    upper q nx ny ≤ lower r nx ny ∨ upper r nx ny ≤ lower q nx ny := by
  by_cases sign : 0≤nx*(centerX r-centerX q)+ny*(centerY r-centerY q)
  · rw [abs_of_nonneg sign] at h
    left; dsimp [upper,lower]; linarith only [h]
  · rw [abs_of_nonpos (le_of_not_ge sign)] at h
    right; dsimp [upper,lower]; linarith only [h]

theorem parallel_radius (q r : OpenSquare) :
    supportRadius q q.c q.s+supportRadius r q.c q.s=pairRadius q r := by
  have hu : q.c*q.c+q.s*q.s=1 := by nlinarith only [q.unit_normal]
  have hz : -q.c*q.s+q.s*q.c=0 := by ring
  have cross : -q.c*r.s+q.s*r.c = -normalCross q r := by
    unfold normalCross; ring
  simp only [supportRadius,hu,hz,abs_one,abs_zero,add_zero,mul_one,
    cross,abs_neg,pairRadius,normalDot]

theorem transverse_radius (q r : OpenSquare) :
    supportRadius q (-q.s) q.c+supportRadius r (-q.s) q.c=pairRadius q r := by
  have hu : -(-q.s)*q.s+q.c*q.c=1 := by nlinarith only [q.unit_normal]
  have hz : -q.s*q.c+q.c*q.s=0 := by ring
  have cross : -q.s*r.c+q.c*r.s=normalCross q r := by unfold normalCross; ring
  have dot : -(-q.s)*r.s+q.c*r.c=normalDot q r := by unfold normalDot; ring
  simp only [supportRadius,hu,hz,abs_one,abs_zero,zero_add,mul_one,
    cross,dot,pairRadius]
  ring

/-- Under the actual triangle anchors, disjointness can only put A's
upper transverse face below B, on one of the two transverse axes. -/
theorem alternatives (A B : OpenSquare)
    (ap : 0 < A.c) (aq : 0 ≤ A.s) (bc : 0 < B.c) (bs : 0 < B.s)
    (same : A.side=B.side)
    (aP : ClosedInside A 2 (113/50)) (aQ : ClosedInside A (113/50) 2)
    (aT : ClosedInside A (47/20) (47/20))
    (bT : ClosedInside B (33/20) (47/20)) (bH : B.Inside 2 (1543/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) :
    upper A (-B.s) B.c ≤ B.loV ∨
      A.loV+A.side ≤ lower B (-A.s) A.c := by
  have hH : ClosedInside B 2 (1543/500) :=
    ⟨bH.1.le,bH.2.1.le,bH.2.2.1.le,bH.2.2.2.le⟩
  have axes := CongruentSAT.faceSeparation_of_disjoint A B same apart
  change pairRadius A B ≤ |A.c*(centerX B-centerX A)+A.s*(centerY B-centerY A)| ∨
    pairRadius A B ≤ |-A.s*(centerX B-centerX A)+A.c*(centerY B-centerY A)| ∨
    pairRadius B A ≤ |B.c*(centerX B-centerX A)+B.s*(centerY B-centerY A)| ∨
    pairRadius B A ≤ |-B.s*(centerX B-centerX A)+B.c*(centerY B-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius B nx ny=R)
      (sep : R ≤ |nx*(centerX B-centerX A)+ny*(centerY B-centerY A)|) :=
    separated A B nx ny (by rwa [identity])
  rcases axes with au | av | bu | bv
  · have sep := separateAxis A.c A.s _ (parallel_radius A B) au
    have aTopBounds := closed_bounds A _ _ A.c A.s aT
    have bt := closed_bounds B _ _ A.c A.s bT
    have ah := closed_bounds A _ _ A.c A.s aP
    have bh := strict_bounds B _ _ A.c A.s A.unit_normal bH
    rcases sep with sep | sep <;> exfalso <;>
      nlinarith only [sep,aTopBounds.2,bt.1,ah.1,bh.2,ap,aq]
  · have sep := separateAxis (-A.s) A.c _ (transverse_radius A B) av
    have ah := closed_bounds A _ _ (-A.s) A.c aQ
    have bh := closed_bounds B _ _ (-A.s) A.c hH
    rcases sep with sep | sep
    · right; simpa only [(ownV A).2] using sep
    · exfalso; nlinarith only [sep,ah.1,bh.2,ap,aq]
  · have identity : supportRadius A B.c B.s+supportRadius B B.c B.s=pairRadius B A := by
      rw [add_comm]; exact parallel_radius B A
    have sep := separateAxis B.c B.s _ identity bu
    have aTopBounds := closed_bounds A _ _ B.c B.s aT
    have bt := closed_bounds B _ _ B.c B.s bT
    have ah := closed_bounds A _ _ B.c B.s aP
    have bh := closed_bounds B _ _ B.c B.s hH
    rcases sep with sep | sep <;> exfalso <;>
      nlinarith only [sep,aTopBounds.2,bt.1,ah.1,bh.2,bc,bs]
  · have identity : supportRadius A (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B A := by
      rw [add_comm]; exact transverse_radius B A
    have sep := separateAxis (-B.s) B.c _ identity bv
    have ah := closed_bounds A _ _ (-B.s) B.c aQ
    have bh := closed_bounds B _ _ (-B.s) B.c hH
    rcases sep with sep | sep
    · left; simpa only [(ownV B).1] using sep
    · exfalso; nlinarith only [sep,ah.1,bh.2,bc,bs]

end N12Compact.ABTransverse
