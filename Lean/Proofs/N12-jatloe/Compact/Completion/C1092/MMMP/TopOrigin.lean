import Compact.Completion.C1092.MMMP.TopOriginSign
import Compact.Completion.C1092.MMMP.NegativeCornerFloor
import Compact.Completion.C1092.MMMP.CornerFloorProfile

/-! The genuine left-wall/corner interaction supplies the top wall's
origin in the MMMP branch. Each chart retains its original square owner;
the final transfer uses a proved support profile, not an assumed face. -/
namespace N12Compact.C1092MMMPTopOrigin
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

private theorem canonical_support_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0<r.c ∧ |r.s|≤r.c ∧ r.side=q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) ∧
      (∀ nx ny, upper r nx ny=upper q nx ny) := by
  obtain ⟨r,cp,sn,shape,inside,support⟩ :=
    Completion.OtherCases.WallProfile.positive_frame q
  by_cases order : r.s≤r.c
  · exact ⟨r,cp,by simpa only [abs_of_nonneg sn] using order,shape,inside,support⟩
  · refine ⟨turnFrame (turnFrame (turnFrame r)),?_,?_,by simpa using shape,?_,?_⟩
    · simpa [turnFrame] using cp.trans (lt_of_not_ge order)
    · simpa [turnFrame,abs_of_pos cp] using (lt_of_not_ge order).le
    · intro x y
      simpa only [turnFrame_inside] using inside x y
    · intro nx ny
      simpa only [Completion.OtherCases.WallProfile.upper_turnFrame] using support nx ny

private theorem corner_profile (L K : OpenSquare) (side : 1<L.side)
    (cap : L.side≤2) (same : L.side=K.side)
    (dn : Normal L.c (-L.s)) (negative : L.s<0)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (wallL : ∀ x y, L.Inside x y → -1≤x)
    (wallK : ∀ x y, K.Inside x y → -1≤x)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y))
    (nx ny : ℝ) (xn : 0≤nx) (yn : 0≤ny) (unit : nx^2+ny^2=1) :
    K.side*C1092WallProfileScalars.profile nx ny-nx+2*ny≤upper K nx ny := by
  obtain ⟨R,rc,range,shape,inside,support⟩ := canonical_support_frame K
  have sameR : L.side=R.side := same.trans shape.symm
  have H' := (inside _ _).mpr H
  have P' := (inside _ _).mpr P
  have missing' : ¬R.Inside (1/5) 1 := fun own => missing ((inside _ _).mp own)
  have apart' : ∀ x y, ¬(L.Inside x y ∧ R.Inside x y) :=
    fun x y own => apart x y ⟨own.1,(inside x y).mp own.2⟩
  have rn : R.s<0 := by
    by_contra nonnegative
    have sn : 0≤R.s := le_of_not_gt nonnegative
    have normal : Normal R.c R.s :=
      ⟨sn,by simpa only [abs_of_nonneg sn] using range,R.unit_normal⟩
    exact C1092MMMPNegativeCornerFloor.nonnegative_impossible L R side sameR dn negative
      left cut wallL normal G H' P' missing' apart'
  have normal : Normal R.c (-R.s) := ⟨by linarith only [rn],
    by simpa only [abs_of_neg rn] using range,by nlinarith only [R.unit_normal]⟩
  have floor := C1092MMMPNegativeCornerFloor.floor L R side cap sameR dn left cut
    wallL normal G H' P' missing' apart'
  have bound := C1092MMMPCornerFloorProfile.support_profile R
    (by rwa [←sameR]) normal
    (fun x y own => wallK x y ((inside x y).mp own)) H' P' floor nx ny xn yn unit
  simpa only [shape,support] using bound

private theorem chart_support (q : OpenSquare) (c s : ℝ) :
    upper (pullY q) c (-s)=c-2*s+upper (q.translated 1 2) c s := by
  have radius : supportRadius (pullY q) c (-s)=supportRadius q c s := by
    dsimp [supportRadius,pullY]
    rw [show c*q.c+(-s)*(-q.s)=c*q.c+s*q.s by ring,
      show -c*(-q.s)+(-s)*q.c=-(-c*q.s+s*q.c) by ring,abs_neg]
  have reflected : upper (pullY q) c (-s)=upper q c s-4*s := by
    dsimp only [upper]
    rw [center_pullY_x,center_pullY_y,radius]
    ring
  have shifted : upper (q.translated 1 2) c s=upper q c s-c-2*s := by
    dsimp [upper,supportRadius,OpenSquare.translated,centerX,centerY]
    linear_combination -(c+2*s)*q.unit_normal
  rw [reflected,shifted]
  ring

/-- The top-origin point is owned by the actual top-wall square in every
MMMP packing. The independent right near-point exclusion remains separate. -/
theorem point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp) :
    (owners p 11).Inside 2 3 := by
  classical
  by_contra missing
  obtain ⟨L,lp⟩ := C1092MMMPTopOriginSign.negative_left_of_missing_top p hf hb missing
  let Q := (owners p 3).translated 1 2
  have actualQ (x y : ℝ) : Q.Inside x y ↔ (owners p 3).Inside (1+x) (2+y) :=
    inside_translated_iff _ _ _ _ _
  have side : 1<L.side := by rw [lp.side]; exact side_gt p 8
  have cap : L.side≤2 := by
    rw [lp.side]
    change (p.square _).side≤2
    rw [p.congruent]
    linarith only [p.side_le]
  have same : L.side=Q.side := lp.side.trans (side_same p 8 3)
  have wallL : ∀ x y, L.Inside x y → -1≤x := by
    intro x y own
    have bound := p.contained _ _ _ ((lp.actual x y).mp own)
    linarith only [bound.1]
  have wallQ : ∀ x y, Q.Inside x y → -1≤x := by
    intro x y own
    have bound := p.contained _ _ _ ((actualQ x y).mp own)
    linarith only [bound.1]
  have G : L.Inside 0 (2/5) := by
    apply (lp.actual _ _).mpr
    norm_num
    exact C1092MMMPLeftFar.point p hf hb
  have H : Q.Inside 0 (1/2) := by
    apply (actualQ _ _).mpr
    norm_num
    exact C1092MMMPTopOriginSign.corner_halfpoint p hf hb missing
  have corner : (owners p 3).Inside 1 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 3
  have P : Q.Inside 0 1 := by
    apply (actualQ _ _).mpr
    norm_num
    exact corner
  have missQ : ¬Q.Inside (1/5) 1 := by
    intro own
    have h := (actualQ _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 3 11 (by decide) _ _
      ⟨h,C1092MMMPTopOriginSign.top_alternative p hf hb missing⟩
  have apart : ∀ x y, ¬(L.Inside x y ∧ Q.Inside x y) :=
    fun x y own => owners_disjoint p hf 8 3 (by decide) _ _
      ⟨(lp.actual x y).mp own.1,(actualQ x y).mp own.2⟩
  have full := corner_profile L Q side cap same lp.normal lp.negative lp.centerLeft.le
    lp.centerCut wallL wallQ G H P missQ apart
  let B := pullY (owners p 11)
  let K := pullY (owners p 3)
  have boxB : InsideContainer B := container_pullY _ (p.contained _)
  have markerB : (owners p 11).Inside 2 (1543/500) := by
    simpa [marker] using marker_point p hf 11 15 (by decide +kernel)
  have markerK : (owners p 3).Inside 1 (1543/500) := by
    simpa [marker] using marker_point p hf 3 6 (by decide +kernel)
  have profileK (c s : ℝ) (cn : 0≤c) (sn : 0≤s) (unit : c^2+s^2=1) :
      K.side*C1092WallProfileScalars.profile c s≤upper K c (-s) := by
    have bound := full c s cn sn unit
    have identity := chart_support (owners p 3) c s
    change (owners p 3).side*C1092WallProfileScalars.profile c s≤
      upper (pullY (owners p 3)) c (-s)
    change (owners p 3).side*C1092WallProfileScalars.profile c s-c+2*s≤
      upper ((owners p 3).translated 1 2) c s at bound
    linarith only [identity,bound]
  have top := Completion.OtherCases.WallProfile.boundary_origin_of_profile B K
    (457/500) (8/5) (side_gt p 11) (side_same p 11 3)
    (fun x y own => (boxB x y own).2.2.1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [B,inside_pullY]; exact markerB)
    (by norm_num [B,inside_pullY]; exact (top_pair p hf hb).1)
    (by norm_num [K,inside_pullY]; exact markerK)
    (by norm_num [K,inside_pullY]; exact corner) profileK
    (fun x y own => owners_disjoint p hf 3 11 (by decide) _ _
      ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩)
  norm_num [B,inside_pullY] at top
  exact missing top

#print axioms point
end N12Compact.C1092MMMPTopOrigin
