import Compact.Completion.C1092.MixedCornerObstruction
import Compact.Completion.C1092.MMMP.LeftCenterFaces

/-! The genuine left-wall center cut replaces the extra lower-face
hypothesis in the positive-sign wall/corner obstruction. This is a local
two-square theorem; the negative left-wall sign remains a separate case. -/
namespace N12Compact.C1092MMMPCenterCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MixedCornerSupports
set_option Elab.async false

/-- A square centered in the upper-left quadrant extends beyond the
half-unit vertical anchor in every unit up-left direction. -/
theorem up_left (L : OpenSquare) (side : 1<L.side)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : nx≤0) (yn : 0≤ny) :
    ny/2<upper L nx ny := by
  let u := nx*L.c+ny*L.s
  let v := -nx*L.s+ny*L.c
  have uv : u^2+v^2=1 := by
    calc
      _ = (nx^2+ny^2)*(L.c^2+L.s^2) := by dsimp [u,v]; ring
      _ = 1 := by rw [unit,L.unit_normal]; norm_num
  have sum : 1≤|u|+|v| := by
    have product := mul_nonneg (abs_nonneg u) (abs_nonneg v)
    have sqU : |u|^2=u^2 := sq_abs u
    have sqV : |v|^2=v^2 := sq_abs v
    by_contra low
    have small := mul_pos
      (show 0<1-(|u|+|v|) by linarith only [low])
      (show 0<1+(|u|+|v|) by linarith only [abs_nonneg u,abs_nonneg v])
    nlinarith only [uv,sqU,sqV,product,small]
  have radius : 1/2<supportRadius L nx ny := by
    have bound := mul_le_mul_of_nonneg_left sum
      (show 0≤L.side/2 by linarith only [side])
    dsimp [supportRadius]
    dsimp [u,v] at bound
    linarith only [bound,side]
  have ycap : ny≤1 := by nlinarith only [unit,sq_nonneg nx,sq_nonneg (ny-1)]
  have a := mul_nonneg_of_nonpos_of_nonpos xn left
  have b := mul_nonneg yn cut
  dsimp [upper]
  linarith only [radius,ycap,a,b]

/-- The other difficult corner axis uses the actual center cut directly.
No lower face or unproved far wall point is introduced. -/
theorem up_right (L : OpenSquare) (side : 1<L.side)
    (dn : Normal L.c L.s) (rp : 0<L.s) (G : L.Inside 0 (2/5))
    (cut : 0≤centerY L) (c s : ℝ) (cn : Normal c s)
    (ratio : s<(2/5)*c) : c/2<upper L s c := by
  let d := L.c
  let r := L.s
  let alpha := c*d-s*r
  let beta := s*d+c*r
  let A := L.loU+L.side
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [db.1]
  have cp : 0<c := by linarith only [cb.1]
  have ap : 0<alpha := by
    have first := mul_pos dp (show 0<c-s by linarith only [ratio,cp])
    have last := mul_nonneg cn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [alpha,d,r]
    nlinarith only [first,last]
  have bp : 0<beta := add_pos_of_nonneg_of_pos
    (mul_nonneg cn.1 dp.le) (mul_pos cp rp)
  have formula := upper_nn L s c beta alpha
    (by dsimp [beta,d,r]; ring) (by dsimp [alpha,d,r]; ring) bp.le ap.le
  have anchor : (2/5)*r<A := by
    dsimp [r,A]
    linarith only [G.2.1]
  have identity : d*upper L s c=
      s*A+alpha*centerY L+(L.side/2)*alpha*(d+r) := by
    rw [formula]
    dsimp [d,r,alpha,beta,A,centerY]
    linear_combination s*(L.loU+L.side)*L.unit_normal
  have weighted := mul_le_mul_of_nonneg_left anchor.le cn.1
  have centered := mul_nonneg ap.le cut
  have excess := mul_pos (sub_pos.mpr side)
    (mul_pos ap (show 0<d+r by dsimp [d,r]; linarith only [dp,rp]))
  have lower : (2/5)*s*r+(1/2)*alpha*(d+r)<d*upper L s c := by
    nlinarith only [identity,weighted,centered,excess]
  have rise : 1<d+r/2 := by
    have positive := mul_pos rp
      (show 0<d-(3/4)*r by dsimp [d,r]; linarith only [dn.2.1,rp])
    have unitL : d^2+r^2=1 := L.unit_normal
    by_contra low
    have small := mul_nonneg
      (show 0≤1-(d+r/2) by linarith only [low])
      (show 0≤1+(d+r/2) by linarith only [dp,rp])
    nlinarith only [positive,unitL,small]
  have first := mul_pos dp (sub_pos.mpr rise)
  have last := mul_pos rp
    (show 0<d/2-(2/5)*(d+r-4/5) by
      dsimp [d,r]
      linarith only [db.1,db.2.2.2.2.2])
  have scalar : 0<d*(d+r-1)-(2/5)*r*(d+r-4/5) := by
    nlinarith only [first,last]
  have gap := mul_pos cp scalar
  have correction := mul_pos (sub_pos.mpr ratio)
    (mul_pos rp (show 0<d+r-4/5 by
      dsimp [d,r]
      linarith only [db.2.2.2.2.1]))
  have margin : c*d/2<(2/5)*s*r+(1/2)*alpha*(d+r) := by
    dsimp [alpha]
    nlinarith only [gap,correction]
  exact (mul_lt_mul_left dp).mp (by nlinarith only [margin,lower])

private theorem left_blocked (L K : OpenSquare) (side : 1<L.side)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : nx≤0)
    (sep : upper L nx ny≤lower K nx ny) : False := by
  have yp := C1092MixedCornerSupports.upward L K nx ny unit G H sep
  have a := up_left L side left cut nx ny unit xn yp.le
  have b := (strict_bounds K _ _ nx ny unit H).1
  linarith only [a,b,sep]

private theorem reverse_blocked (L K : OpenSquare) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (yn : 0≤ny) (sep : upper K nx ny≤lower L nx ny) : False := by
  have a := (strict_bounds L _ _ nx ny unit G).1
  have b := (strict_bounds K _ _ nx ny unit H).2
  linarith only [a,b,yn,sep]

theorem alternatives (L K : OpenSquare) (side : 1<L.side) (same : L.side=K.side)
    (dn : Normal L.c L.s) (rp : 0<L.s) (kc : 0<K.c)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) :
    L.loU+L.side≤lower K L.c L.s ∨
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
    · exact Or.inl (by simpa only [(ownU L).2] using forward)
    · exact (reverse_blocked L K G H _ _ L.unit_normal rp.le reverse).elim
  · have sep := split (-L.s) L.c _ (transverse_radius L K) lv
    rcases sep with forward | reverse
    · exact (left_blocked L K side left cut G H _ _
        (by nlinarith only [L.unit_normal]) (by linarith only [rp]) forward).elim
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

private theorem nonnegative (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c L.s) (rp : 0<L.s)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (cn : Normal K.c K.s) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  have cb := normal_bounds cn
  have dp : 0<L.c := by linarith only [(normal_bounds dn).1]
  have cp : 0<K.c := by linarith only [cb.1]
  have sideK : 1<K.side := by rwa [←same]
  have capU : K.loU+K.side≤(1/5)*K.c+K.s := by
    apply le_of_not_gt
    intro failure
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [P.1,P.2.2.2,H.2.2.1,failure,cp,cn.1,cn.2.1]
  have sBound : K.s≤3/4 := by
    nlinarith only [(C1092MixedCornerScalars.elementary cn).2.1,cn.1]
  have negativeU : K.loU<0 := by linarith only [capU,sideK,cb.2.1,sBound]
  have upperU : K.loU<(1/5)*K.c+K.s-1 := by linarith only [capU,sideK]
  have lowerV : K.loV<K.c/2 := by linarith only [H.2.2.1]
  have upperV : K.c<K.loV+K.side := by linarith only [P.2.2.2]
  have J : (2/5)*L.s<L.loU+L.side := by linarith only [G.2.1]
  have axes := alternatives L K side same dn rp cp left cut G H apart
  rcases axes with axis | axis | axis
  · let alpha := L.c*K.c+L.s*K.s
    let delta := L.s*K.c-L.c*K.s
    have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos dp cp) (mul_nonneg rp.le cn.1)
    have du : L.c*K.c+L.s*K.s=alpha := rfl
    have dv : -L.c*K.s+L.s*K.c=delta := by dsimp [delta]; ring
    by_cases sign : 0≤delta
    · have support := lower_nn K L.c L.s alpha delta du dv ap.le sign
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonneg_left lowerV.le sign
      have bound : lower K L.c L.s<alpha*((1/5)*K.c+K.s-1)+delta*(K.c/2) := by
        rw [support]
        exact add_lt_add_of_lt_of_le first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*((1/5)*K.c+K.s-1)+delta*(K.c/2)-(2/5)*L.s=
          L.c*((1/5)*K.c^2+(1/2)*K.c*K.s-K.c)+
            L.s*(1/10+(1/2)*K.s^2-K.s+(1/5)*K.c*K.s) := by
        dsimp [alpha,delta]
        linear_combination (1/2)*L.s*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge (C1092MixedCornerScalars.nonnegative_pair dn cn rp).le) positive
    · have sign' : delta≤0 := (lt_of_not_ge sign).le
      have support := lower_pn K L.c L.s alpha delta du dv ap.le sign'
      have first := mul_neg_of_pos_of_neg ap negativeU
      have last := mul_nonpos_of_nonpos_of_nonneg sign' (cp.le.trans upperV.le)
      have negative : lower K L.c L.s<0 := by rw [support]; exact add_neg_of_neg_of_nonpos first last
      have positive : 0<lower K L.c L.s :=
        (mul_pos (by norm_num : (0:ℝ)<2/5) rp).trans (J.trans_le axis)
      exact (not_lt_of_ge negative.le) positive
  · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
    linarith only [bound,axis,upperU,cb.2.1,cb.2.2.2.1]
  · have bound := up_left L side left cut (-K.s) K.c
      (by nlinarith only [K.unit_normal]) (by linarith only [cn.1]) cp.le
    linarith only [axis,bound,lowerV]

private theorem nonpositive (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c L.s) (rp : 0<L.s)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (cn : Normal K.c (-K.s)) (G : L.Inside 0 (2/5))
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  let d := L.c
  let r := L.s
  let c := K.c
  let s := -K.s
  let alpha := d*c-r*s
  let beta := d*s+r*c
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [(normal_bounds dn).1]
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have an : 0≤alpha := by
    calc
      alpha = d*(c-s)+s*(d-r) := by dsimp [alpha]; ring
      _ ≥ 0 := add_nonneg (mul_nonneg dp.le (sub_nonneg.mpr cn.2.1))
        (mul_nonneg cn.1 (sub_nonneg.mpr dn.2.1))
  have bp : 0<beta := add_pos_of_nonneg_of_pos (mul_nonneg dp.le cn.1) (mul_pos rp cp)
  have sideK : 1<K.side := by rwa [←same]
  have du : L.c*K.c+L.s*K.s=alpha := by dsimp [alpha,d,r,c,s]; ring
  have dv : -L.c*K.s+L.s*K.c=beta := by dsimp [beta,d,r,c,s]; ring
  have support := lower_nn K L.c L.s alpha beta du dv an bp.le
  have J : (2/5)*r<L.loU+L.side := by dsimp [r]; linarith only [G.2.1]
  have lowV : K.loV<c/2 := by dsimp [c]; linarith only [H.2.2.1]
  have lowU : K.loU< -s := by dsimp [s]; linarith only [P.1]
  have exits : K.loU+K.side≤(1/5)*c-s ∨ K.loV+K.side≤c+(1/5)*s := by
    by_cases first : K.loU+K.side≤(1/5)*c-s
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro second
      apply missing
      dsimp [OpenSquare.Inside,InBands]
      dsimp [c,s] at first second lowU lowV
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [first,second,lowU,lowV,cp,cn.1]
  have axes := alternatives L K side same dn rp cp left cut G H apart
  rcases exits with upperU | upperV
  · have ratio : s<(2/5)*c := by
      have owned := H.2.1
      change K.c*0+K.s*(1/2)<K.loU+K.side at owned
      dsimp [s,c] at upperU ⊢
      linarith only [upperU,owned]
    have margin := C1092MixedCornerScalars.upper_u_pair dn cn rp ratio
    have U : K.loU<(1/5)*c-s-1 := by linarith only [upperU,sideK]
    rcases axes with axis | axis | axis
    · have first := mul_le_mul_of_nonneg_left U.le an
      have last := mul_lt_mul_of_pos_left lowV bp
      have bound : lower K L.c L.s<alpha*((1/5)*c-s-1)+beta*(c/2) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*((1/5)*c-s-1)+beta*(c/2)-(2/5)*r=
          d*((1/5)*c^2-(1/2)*c*s-c)+r*(1/10+(1/2)*s^2+s-(1/5)*c*s) := by
        dsimp [alpha,beta]
        linear_combination (1/2)*r*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge margin.2.2.le) positive
    · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
      linarith only [axis,bound,H.1,cn.1]
    · have half := up_right L side dn rp G cut c s cn ratio
      change upper L s c≤K.loV at axis
      exact (not_lt_of_ge (axis.trans lowV.le)) half
  · have V : K.loV<c+(1/5)*s-1 := by linarith only [upperV,sideK]
    rcases axes with axis | axis | axis
    · have first := mul_le_mul_of_nonneg_left lowU.le an
      have last := mul_lt_mul_of_pos_left V bp
      have bound : lower K L.c L.s<alpha*(-s)+beta*(c+(1/5)*s-1) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*(-s)+beta*(c+(1/5)*s-1)-(2/5)*r=
          d*((1/5)*s^2-s)+r*(3/5-c+(1/5)*c*s) := by
        dsimp [alpha,beta]
        linear_combination r*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge (C1092MixedCornerScalars.upper_v_pair dn cn rp).le) positive
    · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
      linarith only [axis,bound,H.1,cn.1]
    · have bound := (strict_bounds L _ _ (-K.s) K.c
        (by nlinarith only [K.unit_normal]) G).2
      dsimp [s,c] at V
      linarith only [axis,bound,V,cb.2.1,cb.2.2.2.1]

/-- The positive-sign left wall contradicts the two actual corner
anchors and its upper-right omission, using only its genuine center. -/
theorem impossible (L K : OpenSquare) (side : 1<L.side) (same : L.side=K.side)
    (dn : Normal L.c L.s) (rp : 0<L.s)
    (left : centerX L≤0) (cut : 0≤centerY L)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2)) (P : K.Inside 0 1)
    (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  obtain ⟨R,rc,range,rside,rinside,_⟩ := ClosedFrames.canonical_frame K
  have sameR : L.side=R.side := same.trans rside.symm
  have h := (rinside _ _).mpr H
  have p := (rinside _ _).mpr P
  have missingR : ¬R.Inside (1/5) 1 := fun owned => missing ((rinside _ _).mp owned)
  have apartR : ∀ x y, ¬(L.Inside x y ∧ R.Inside x y) :=
    fun x y owned => apart x y ⟨owned.1,(rinside x y).mp owned.2⟩
  by_cases sign : 0≤R.s
  · exact nonnegative L R side sameR dn rp left cut
      ⟨sign,(abs_le.mp range).2,R.unit_normal⟩ G h p missingR apartR
  · exact nonpositive L R side sameR dn rp left cut
      ⟨by linarith only [sign],by linarith only [(abs_le.mp range).1],
        by nlinarith only [R.unit_normal]⟩ G h p missingR apartR

#print axioms up_right
#print axioms impossible
end N12Compact.C1092MMMPCenterCorner
