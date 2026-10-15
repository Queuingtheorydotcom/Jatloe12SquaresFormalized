import Compact.Completion.C1092.MixedCornerScalars

/-! Exact whole-square supports for the mixed wall. The genuine lower
face and foreign halfpoint exclude every up-left separating direction. -/
namespace N12Compact.C1092MixedCornerSupports
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic C1092WholeSupports
set_option Elab.async false

theorem upper_nn (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0≤d) (en : 0≤e) :
    upper Q nx ny=d*(Q.loU+Q.side)+e*(Q.loV+Q.side) := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_left dn,max_eq_left en]
  ring

theorem negative_support (Q : OpenSquare) (nx ny : ℝ) :
    lower Q (-nx) (-ny)=-upper Q nx ny ∧
      upper Q (-nx) (-ny)=-lower Q nx ny := by
  have u : (-nx)*Q.c+(-ny)*Q.s=-(nx*Q.c+ny*Q.s) := by ring
  have v : -(-nx)*Q.s+(-ny)*Q.c=-(-nx*Q.s+ny*Q.c) := by ring
  constructor <;> dsimp [lower,upper,supportRadius] <;> rw [u,v,abs_neg,abs_neg] <;> ring

theorem upper_cap (L : OpenSquare) (side : 1<L.side)
    (dn : Normal L.c L.s) (rp : 0<L.s)
    (G : L.Inside 0 (2/5)) (face : -(2/5)*L.c≤L.loV)
    (H : ¬L.Inside 0 (1/2)) : L.loU+L.side≤L.s/2 := by
  have db := normal_bounds dn
  have dp : 0<L.c := by linarith only [db.1]
  apply le_of_not_gt
  intro failure
  apply H
  dsimp [OpenSquare.Inside,InBands] at G ⊢
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [G.1,G.2.2.1,failure,rp,dp,face,side,db.2.1]

theorem up_left (L : OpenSquare) (side : 1<L.side)
    (dn : Normal L.c L.s) (rp : 0<L.s)
    (G : L.Inside 0 (2/5)) (face : -(2/5)*L.c≤L.loV)
    (cap : L.loU+L.side≤L.s/2)
    (c s : ℝ) (cp : 0<c) (sn : 0≤s) : c/2<upper L (-s) c := by
  let d := L.c
  let r := L.s
  let k := c*r-s*d
  let alpha := c*d+s*r
  have db := normal_bounds dn
  have dp : 0<d := by dsimp [d]; linarith only [db.1]
  have ap : 0<alpha :=
    add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg sn rp.le)
  have common := C1092MixedCornerScalars.common dn rp
  have u : (-s)*L.c+c*L.s=k := by dsimp [k,d,r]; ring
  have v : -(-s)*L.s+c*L.c=alpha := by dsimp [alpha,d,r]; ring
  have J : (2/5)*r<L.loU+L.side := by
    calc
      (2/5)*r = L.c*0+L.s*(2/5) := by dsimp [r]; ring
      _ < L.loU+L.side := G.2.1
  have V : 1-(2/5)*d<L.loV+L.side := by
    dsimp [d]
    linarith only [face,side]
  by_cases sign : 0≤k
  · have support := upper_nn L (-s) c k alpha u v sign ap.le
    have first := mul_le_mul_of_nonneg_left J.le sign
    have last := mul_lt_mul_of_pos_left V ap
    have bound : k*((2/5)*r)+alpha*(1-(2/5)*d)<upper L (-s) c := by
      rw [support]
      exact add_lt_add_of_le_of_lt first last
    have identity : k*((2/5)*r)+alpha*(1-(2/5)*d)-c/2=
        c*(d-9/10+(4/5)*r^2)+s*(r*(1-(4/5)*d)) := by
      dsimp [k,alpha,d,r]
      linear_combination -(2/5)*c*dn.2.2
    have p : 0<c*(d-9/10+(4/5)*r^2) := mul_pos cp
      ((show (0:ℝ)<1/10 by norm_num).trans_le common.1)
    have q : 0≤s*(r*(1-(4/5)*d)) := mul_nonneg sn common.2.1.le
    have positive := add_pos_of_pos_of_nonneg p q
    exact (sub_pos.mp (by rw [identity]; exact positive)).trans bound
  · have kn : k≤0 := (lt_of_not_ge sign).le
    have support := upper_np L (-s) c k alpha u v kn ap.le
    have lowU : L.loU≤r/2-L.side := by dsimp [r]; linarith only [cap]
    have first := mul_le_mul_of_nonpos_left lowU kn
    have last := mul_le_mul_of_nonneg_left
      (show L.side-(2/5)*d≤L.loV+L.side by dsimp [d]; linarith only [face]) ap.le
    have excess := mul_pos (sub_pos.mpr side)
      (show 0<alpha-k by linarith only [ap,sign])
    have bound : k*(r/2-1)+alpha*(1-(2/5)*d)<upper L (-s) c := by
      have weighted : k*(r/2-L.side)+alpha*(L.side-(2/5)*d)≤upper L (-s) c := by
        rw [support]
        exact add_le_add first last
      apply lt_of_lt_of_le _ weighted
      apply sub_pos.mp
      convert excess using 1 <;> ring
    have identity : k*(r/2-1)+alpha*(1-(2/5)*d)-c/2=
        c*(d-r-(9/10)*d^2)+s*(d+r-(9/10)*d*r) := by
      dsimp [k,alpha,d,r]
      linear_combination (1/2)*c*dn.2.2
    have factor : d*(c*(d-r-(9/10)*d^2)+s*(d+r-(9/10)*d*r))=
        c*(1-(9/10)*d)+(d+r-(9/10)*d*r)*(s*d-c*r) := by
      dsimp [d,r]
      linear_combination c*(1-(9/10)*L.c)*dn.2.2
    have a : 0<c*(1-(9/10)*d) := mul_pos cp (by dsimp [d]; linarith only [db.2.1])
    have b : 0<(d+r-(9/10)*d*r)*(s*d-c*r) := mul_pos common.2.2.1
      (by dsimp [k] at sign; linarith only [sign])
    have product : 0<d*(c*(d-r-(9/10)*d^2)+s*(d+r-(9/10)*d*r)) := by
      rw [factor]
      exact add_pos a b
    have positive : 0<c*(d-r-(9/10)*d^2)+s*(d+r-(9/10)*d*r) := by
      by_contra failure
      have weak := mul_nonpos_of_nonneg_of_nonpos dp.le (le_of_not_gt failure)
      linarith only [product,weak]
    exact (sub_pos.mp (by rw [identity]; exact positive)).trans bound

theorem upward (L K : OpenSquare) (nx ny : ℝ) (unit : nx^2+ny^2=1)
    (G : L.Inside 0 (2/5)) (H : K.Inside 0 (1/2))
    (sep : upper L nx ny≤lower K nx ny) : 0<ny := by
  have a := (strict_bounds L _ _ nx ny unit G).2
  have b := (strict_bounds K _ _ nx ny unit H).1
  linarith only [a,b,sep]

#print axioms up_left
end N12Compact.C1092MixedCornerSupports
