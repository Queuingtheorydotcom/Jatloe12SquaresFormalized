import Compact.Completion.C1092.MMMP.CenterCorner

/-! Support supplied by the genuine center cut and physical left wall.
No absent corner face is assumed. -/
namespace N12Compact.C1092MMMPNegativeCenterSupports
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MixedCornerSupports
set_option Elab.async false

private theorem radius_scalar {d r c s : ℝ} (dn : Normal d r)
    (cn : Normal c s) :
    c+s≤s*(d+r)+|s*d-c*r|+(s*r+c*d) := by
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<d := by linarith only [db.1]
  have cp : 0<c := by linarith only [cb.1]
  have q : 0≤(1-d)*(1-r)+r^2 := by
    have h := mul_nonneg (sub_nonneg.mpr db.2.1)
      (sub_nonneg.mpr db.2.2.2.1)
    nlinarith only [h,sq_nonneg r]
  have first := mul_nonneg cp.le q
  by_cases sign : 0≤s*d-c*r
  · rw [abs_of_nonneg sign]
    have last := mul_nonneg sign
      (show 0≤2*(d+r)-1 by linarith only [db.2.2.2.2.1])
    have identity : d*(s*(d+r)+(s*d-c*r)+(s*r+c*d)-c-s)=
        c*((1-d)*(1-r)+r^2)+(s*d-c*r)*(2*(d+r)-1) := by
      linear_combination c*dn.2.2
    have h : 0≤d*(s*(d+r)+(s*d-c*r)+(s*r+c*d)-c-s) := by
      rw [identity]
      exact add_nonneg first last
    have h' := nonneg_of_mul_nonneg_right h dp
    linarith only [h']
  · have an : s*d-c*r≤0 := le_of_not_ge sign
    rw [abs_of_nonpos an]
    by_cases rise : 0≤2*r-1
    · have a := mul_nonneg cp.le (sub_nonneg.mpr db.2.2.2.2.1)
      have b := mul_nonneg cn.1 rise
      nlinarith only [a,b]
    · have last := mul_nonneg_of_nonpos_of_nonpos an (le_of_not_ge rise)
      have identity : d*(s*(d+r)-(s*d-c*r)+(s*r+c*d)-c-s)=
          c*((1-d)*(1-r)+r^2)+(s*d-c*r)*(2*r-1) := by
        linear_combination c*dn.2.2
      have h : 0≤d*(s*(d+r)-(s*d-c*r)+(s*r+c*d)-c-s) := by
        rw [identity]
        exact add_nonneg first last
      have h' := nonneg_of_mul_nonneg_right h dp
      linarith only [h']

/-- Every canonical up-right direction has the correlated support floor
forced by the actual left wall and nonnegative center ordinate. -/
theorem up_right (L : OpenSquare) (dn : Normal L.c (-L.s))
    (wall : ∀ x y, L.Inside x y → -1≤x)
    (cut : 0≤centerY L) (c s : ℝ) (cn : Normal c s) :
    L.side*(c+s)/2-s≤upper L s c := by
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<L.c := by linarith only [db.1]
  have cp : 0<c := by linarith only [cb.1]
  have sn : L.s≤0 := by linarith only [dn.1]
  have box := square_support_bound L (-1) 0 1
    (by intro x y own; have h := wall x y own; linarith only [h])
  norm_num [squareRadius,abs_of_pos dp,abs_of_nonpos sn] at box
  have left : -1+L.side*(L.c+(-L.s))/2≤centerX L := by
    linarith only [box]
  have horizontal := mul_le_mul_of_nonneg_left left cn.1
  have vertical := mul_nonneg cp.le cut
  have scalar := mul_le_mul_of_nonneg_left (radius_scalar dn cn)
    (show 0≤L.side/2 by linarith only [L.side_pos])
  have transverse : 0≤-s*L.s+c*L.c := by
    have h := mul_nonneg cn.1 dn.1
    have k := mul_nonneg cp.le dp.le
    nlinarith only [h,k]
  dsimp [upper,supportRadius]
  rw [abs_of_nonneg transverse,
    show s*L.c+c*L.s=s*L.c-c*(-L.s) by ring]
  nlinarith only [horizontal,vertical,scalar]

theorem left_blocked (L K : OpenSquare) (side : 1<L.side)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : nx≤0)
    (sep : upper L nx ny≤lower K nx ny) : False := by
  have yp := upward L K nx ny unit G H sep
  have a := C1092MMMPCenterCorner.up_left L side left cut nx ny unit xn yp.le
  have b := (strict_bounds K _ _ nx ny unit H).1
  linarith only [a,b,sep]

private theorem reverse_blocked (L K : OpenSquare) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (yn : 0≤ny) (sep : upper K nx ny≤lower L nx ny) : False := by
  have a := (strict_bounds L _ _ nx ny unit G).1
  have b := (strict_bounds K _ _ nx ny unit H).2
  linarith only [a,b,yn,sep]

/-- For the negative left-wall sign, only its up-right transverse axis
or one of the corner's two forward axes can separate. -/
theorem alternatives (L K : OpenSquare) (side : 1<L.side) (same : L.side=K.side)
    (dn : Normal L.c (-L.s)) (kc : 0<K.c)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) :
    L.loV+L.side≤lower K (-L.s) L.c ∨
      upper L K.c K.s≤K.loU ∨ upper L (-K.s) K.c≤K.loV := by
  have dp : 0<L.c := by linarith only [(normal_bounds dn).1]
  have all := CongruentSAT.faceSeparation_of_disjoint L K same apart
  change pairRadius L K≤|L.c*(centerX K-centerX L)+L.s*(centerY K-centerY L)| ∨
    pairRadius L K≤|-L.s*(centerX K-centerX L)+L.c*(centerY K-centerY L)| ∨
    pairRadius K L≤|K.c*(centerX K-centerX L)+K.s*(centerY K-centerY L)| ∨
    pairRadius K L≤|-K.s*(centerX K-centerX L)+K.c*(centerY K-centerY L)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius L nx ny+supportRadius K nx ny=radius)
      (sep : radius≤|nx*(centerX K-centerX L)+ny*(centerY K-centerY L)|) :=
    separated L K nx ny (by rwa [identity])
  rcases all with lu | lv | ku | kv
  · have sep := split L.c L.s _ (parallel_radius L K) lu
    rcases sep with forward | reverse
    · have yp := upward L K _ _ L.unit_normal G H forward
      linarith only [yp,dn.1]
    · have flipped : upper L (-L.c) (-L.s)≤lower K (-L.c) (-L.s) := by
        rw [(negative_support L L.c L.s).2,(negative_support K L.c L.s).1]
        exact neg_le_neg reverse
      exact (left_blocked L K side left cut G H _ _
        (by nlinarith only [L.unit_normal]) (by linarith only [dp]) flipped).elim
  · have sep := split (-L.s) L.c _ (transverse_radius L K) lv
    rcases sep with forward | reverse
    · exact Or.inl (by simpa only [(ownV L).2] using forward)
    · exact (reverse_blocked L K G H _ _ (by nlinarith only [L.unit_normal]) dp.le reverse).elim
  · have identity : supportRadius L K.c K.s+supportRadius K K.c K.s=pairRadius K L := by
      rw [add_comm]
      exact parallel_radius K L
    have sep := split K.c K.s _ identity ku
    rcases sep with forward | reverse
    · exact Or.inr (Or.inl (by simpa only [(ownU K).1] using forward))
    · have flipped : upper L (-K.c) (-K.s)≤lower K (-K.c) (-K.s) := by
        rw [(negative_support L K.c K.s).2,(negative_support K K.c K.s).1]
        exact neg_le_neg reverse
      exact (left_blocked L K side left cut G H _ _
        (by nlinarith only [K.unit_normal]) (by linarith only [kc]) flipped).elim
  · have identity : supportRadius L (-K.s) K.c+supportRadius K (-K.s) K.c=pairRadius K L := by
      rw [add_comm]
      exact transverse_radius K L
    have sep := split (-K.s) K.c _ identity kv
    rcases sep with forward | reverse
    · exact Or.inr (Or.inr (by simpa only [(ownV K).1] using forward))
    · exact (reverse_blocked L K G H _ _ (by nlinarith only [K.unit_normal]) kc.le reverse).elim

#print axioms up_right
#print axioms alternatives
end N12Compact.C1092MMMPNegativeCenterSupports
