import Compact.Geometry.PositiveBottomSupport

/-! Both longitudinal ways in which the actual positive bottom
singleton precedes a positive bottom wall contradict the central
negative neighbor's transverse separator. -/
namespace N12Compact.PositiveBottomWallCentralAxis

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem disk {d r c t : ℝ} (dn : Normal d r) (bn : Normal c t) :
    0≤1-c*(2-d-r)-t*(1-d+r/2) := by
  have db := normal_bounds dn
  have defect := mul_nonneg (sub_nonneg.mpr db.2.1)
    (show 0≤(59/100)*d-41/100 by linarith only [db.1])
  have delta : 1-d≤(59/100)*r^2 := by nlinarith only [defect,dn.2.2]
  have small : r≤5/7 := by linarith only [dn.2.1,db.2.2.2.2.2]
  have square := mul_nonneg dn.1 (sub_nonneg.mpr small)
  have cross := mul_nonneg dn.1 (sub_nonneg.mpr db.2.1)
  have norm : (2-d-r)^2+(1-d+r/2)^2≤1 := by
    have identity : (2-d-r)^2+(1-d+r/2)^2-1=
        6*(1-d)-3*r+d*r-(3/4)*r^2 := by
      linear_combination 2*dn.2.2
    nlinarith only [identity,delta,square,cross,dn.1]
  nlinarith only [norm,bn.2.2,sq_nonneg ((2-d-r)-c),sq_nonneg ((1-d+r/2)-t)]

/-- The wall-owned incoming separator needs only this support entrance.
It is supplied by either sign of the actual bottom singleton. -/
theorem of_entry (D B : OpenSquare) (t : ℝ)
    (dn : Normal D.c D.s) (bn : Normal B.c t) (same : D.side=B.side)
    (side : 1<D.side) (box : InsideContainer D)
    (cap : B.loV+B.side≤2*B.c+3*t)
    (entry : 2*D.c+D.s/2≤D.loU)
    (outgoing : upper D t B.c≤B.loV) : False := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0<D.c := by linarith only [db.1]
  have bc : 0≤B.c := by linarith only [bb.1]
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dp.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  let P := t*D.c+B.c*D.s
  let Q := B.c*D.c-t*D.s
  have pp : 0≤P := by
    dsimp [P]
    exact add_nonneg (mul_nonneg bn.1 dp.le) (mul_nonneg bc dn.1)
  have qp : 0≤Q := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [Q]; nlinarith only [first,last]
  have formula : upper D t B.c=P*(D.loU+D.side)+Q*(D.loV+D.side) := by
    rw [upper_in_bands]
    have u : t*D.c+B.c*D.s=P := rfl
    have v : -t*D.s+B.c*D.c=Q := by dsimp [Q]; ring
    rw [u,v,abs_of_nonneg pp,abs_of_nonneg qp]; ring
  have exit : upper D t B.c+D.side≤2*B.c+3*t := by
    rw [←same] at cap
    linarith only [outgoing,cap]
  have advance := mul_nonneg bn.1 (sub_nonneg.mpr entry)
  have floorWeight := mul_nonneg qp wall
  have width := mul_pos (sub_pos.mpr side)
    (mul_pos dp (show 0<1+P+Q by linarith only [pp,qp]))
  have diskWeight := mul_nonneg dp.le (disk dn bn)
  have correction := mul_nonneg (mul_nonneg bn.1 dn.1) (sub_nonneg.mpr db.2.1)
  have residual : 0≤D.c*(1+P+Q-2*B.c-t)+t*D.s/2 := by
    dsimp [P,Q] at diskWeight ⊢
    nlinarith only [diskWeight,correction]
  have identity : D.c*(upper D t B.c+D.side-(2*B.c+3*t))=
      t*(D.loU-(2*D.c+D.s/2))+Q*(D.s*D.loU+D.c*D.loV)+
      (D.side-1)*D.c*(1+P+Q)+D.c*(1+P+Q-2*B.c-t)+t*D.s/2 := by
    rw [formula]
    dsimp [P,Q]
    linear_combination t*D.loU*dn.2.2
  have limit := mul_nonneg dp.le (sub_nonneg.mpr exit)
  nlinarith only [identity,advance,floorWeight,width,residual,limit]

theorem impossible (O D B : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (dn : Normal D.c D.s) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side) (side : 1<O.side)
    (corner : O.loV+O.side≤O.c-O.s)
    (bottom : 0≤O.s*O.loU+O.c*O.loV) (box : InsideContainer D)
    (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : O.loU+O.side≤lower D O.c O.s ∨ upper O D.c D.s≤D.loU)
    (outgoing : upper D t B.c≤B.loV) : False := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have op : 0<O.c := by linarith only [ob.1]
  have dp : 0<D.c := by linarith only [db.1]
  have bc : 0≤B.c := by linarith only [bb.1]
  have ds : 1<D.side := by simpa only [sameOD] using side
  have wall : 0≤D.s*D.loU+D.c*D.loV := by
    have lower : ∀ x y, D.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds D dp.le dn.1 lower).2
    dsimp [centerY] at boundary
    nlinarith only [boundary]
  let P := t*D.c+B.c*D.s
  let Q := B.c*D.c-t*D.s
  have pp : 0≤P := by
    dsimp [P]
    exact add_nonneg (mul_nonneg bn.1 dp.le) (mul_nonneg bc dn.1)
  have qp : 0≤Q := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [Q]; nlinarith only [first,last]
  have upperFormula : upper D t B.c=P*(D.loU+D.side)+Q*(D.loV+D.side) := by
    rw [upper_in_bands]
    have u : t*D.c+B.c*D.s=P := rfl
    have v : -t*D.s+B.c*D.c=Q := by dsimp [Q]; ring
    rw [u,v,abs_of_nonneg pp,abs_of_nonneg qp]; ring
  have exit : upper D t B.c+D.side≤2*B.c+3*t := by
    rw [←sameDB] at cap
    linarith only [outgoing,cap]
  have scalar := disk dn bn
  rcases incoming with own | next
  · let K := O.c*D.c+O.s*D.s
    let H := O.s*D.c-O.c*D.s
    let m := min H 0
    have kp : 0≤K := by
      dsimp [K]
      exact add_nonneg (mul_nonneg op.le dp.le) (mul_nonneg on.1 dn.1)
    have mn : m≤0 := min_le_right _ _
    have lowerFormula : lower D O.c O.s=K*D.loU+H*D.loV+m*D.side := by
      rw [lower_in_bands]
      have u : O.c*D.c+O.s*D.s=K := rfl
      have v : -O.c*D.s+O.s*D.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp]
      by_cases hp : 0≤H
      · rw [abs_of_nonneg hp]
        have value : m=0 := min_eq_right hp
        rw [value]; ring
      · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
        rw [abs_of_nonpos hn]
        have value : m=H := min_eq_left hn
        rw [value]; ring
    have entry := PositiveBottomSupport.own_axis O on side corner bottom
    have advance := mul_nonneg bn.1
      (show 0≤lower D O.c O.s-(2*O.c+O.s/2) by linarith only [entry,own])
    let beta := O.c*B.c-O.s*t
    have betaPos : 0≤beta := by
      have first := mul_nonneg bc (sub_nonneg.mpr on.2.1)
      have last := mul_nonneg on.1 (sub_nonneg.mpr bn.2.1)
      dsimp [beta]; nlinarith only [first,last]
    have floorWeight := mul_nonneg betaPos wall
    let G := O.c*(1+P+Q)-t*m
    have gp : 0<G := by
      have first := mul_pos op (show 0<1+P+Q by linarith only [pp,qp])
      have last := mul_nonneg bn.1 (neg_nonneg.mpr mn)
      dsimp [G]; nlinarith only [first,last]
    have width := mul_pos (sub_pos.mpr ds) gp
    have correction : 0≤O.s/2-O.c*D.s/2-m := by
      by_cases hp : 0≤H
      · have value : m=0 := min_eq_right hp
        have product := mul_nonneg on.1 (sub_nonneg.mpr db.2.1)
        dsimp [H] at hp
        rw [value]
        nlinarith only [hp,product]
      · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
        have value : m=H := min_eq_left hn
        have product := mul_nonneg on.1 (sub_nonneg.mpr db.2.1)
        rw [value]
        dsimp [H] at hn ⊢
        nlinarith only [hn,product]
    have correctionWeight := mul_nonneg bn.1 correction
    have diskWeight := mul_nonneg op.le scalar
    have residual : 0≤G+t*(2*O.c+O.s/2)-O.c*(2*B.c+3*t) := by
      dsimp [G,P,Q] at correctionWeight diskWeight ⊢
      nlinarith only [correctionWeight,diskWeight]
    have identity : O.c*(upper D t B.c+D.side-(2*B.c+3*t))=
        t*(lower D O.c O.s-(2*O.c+O.s/2))+
        beta*(D.s*D.loU+D.c*D.loV)+(D.side-1)*G+
        (G+t*(2*O.c+O.s/2)-O.c*(2*B.c+3*t)) := by
      rw [upperFormula,lowerFormula]
      dsimp [K,H,beta,G,P,Q]; ring
    have limit := mul_nonneg op.le (sub_nonneg.mpr exit)
    nlinarith only [identity,advance,floorWeight,width,residual,limit]
  · have entry := PositiveBottomSupport.positive_projection O on dn side corner bottom
    exact of_entry D B t dn bn sameDB ds box cap
      (by linarith only [entry,next]) outgoing

/-- The negative singleton's wall-owned longitudinal separator is
excluded without any upper bound on its tilt. -/
theorem negative_bottom_wall_axis (O D B : OpenSquare) (q t : ℝ)
    (signed : O.s=-q) (on : Normal O.c q)
    (dn : Normal D.c D.s) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side)
    (side : 1<O.side) (corner : O.c-q≤O.loU)
    (bottom : q*(O.loU+O.side)≤O.c*O.loV)
    (box : InsideContainer D) (cap : B.loV+B.side≤2*B.c+3*t)
    (incoming : upper O D.c D.s≤D.loU)
    (outgoing : upper D t B.c≤B.loV) : False := by
  have entry := PositiveBottomSupport.negative_frame_projection O q signed on dn
    side corner bottom
  exact of_entry D B t dn bn sameDB (by simpa only [sameOD] using side) box cap
    (by linarith only [entry,incoming]) outgoing

#print axioms of_entry
#print axioms impossible
#print axioms negative_bottom_wall_axis
end N12Compact.PositiveBottomWallCentralAxis
