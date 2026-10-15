import Compact.Geometry.FullAuxWallPositiveTransverse
import Compact.Geometry.FullAuxWallPositiveTopMargins
import Compact.Geometry.FullAuxWallTopEndpoint

/-! Genuine upper and lower faces of the positive outer square. These
follow from the two actual transverse C/B selectors and foreign points
owned by the top wall, paired corner, and left wall. -/
namespace N12Compact.FullAuxWallPositiveTop

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic FullAuxWallTopEndpoint
set_option Elab.async false

private theorem upper_pp (q : OpenSquare) (x y : ℝ)
    (hu : 0≤x*q.c+y*q.s) (hv : 0≤-x*q.s+y*q.c) :
    upper q x y=(x*q.c+y*q.s)*(q.loU+q.side)+(-x*q.s+y*q.c)*(q.loV+q.side) := by
  dsimp [upper,supportRadius,centerX,centerY]
  rw [abs_of_nonneg hu,abs_of_nonneg hv]
  ring

private theorem upper_np (q : OpenSquare) (x y : ℝ)
    (hu : x*q.c+y*q.s≤0) (hv : 0≤-x*q.s+y*q.c) :
    upper q x y=(x*q.c+y*q.s)*q.loU+(-x*q.s+y*q.c)*(q.loV+q.side) := by
  dsimp [upper,supportRadius,centerX,centerY]
  rw [abs_of_nonpos hu,abs_of_nonneg hv]
  ring

theorem endpoint_v (D B : OpenSquare)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (hd : 1<D.side) (hb : 1<B.side)
    (center : D.Inside 2 2)
    (excess : D.loU+D.side-2*(D.c+D.s)<1/10)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (low : B.Inside 1 (113/50)) (marker : B.Inside (33/20) (47/20))
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV) :
    3*B.c-(8/5)*B.s<B.loV+B.side := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dc : 0<D.c := by linarith only [db.1]
  have bc : 0<B.c := by linarith only [bb.1]
  have dS := dn.1
  have bt := bn.1
  let alpha := D.c*B.c+D.s*B.s
  let beta := D.c*B.s-D.s*B.c
  have ap : 0<alpha := by dsimp [alpha]; positivity
  have lower : 1+D.c-(8/5)*D.s<D.loV+D.side := by linarith only [bottom,hd]
  apply lt_of_not_ge
  intro cap
  have vlo : B.loV≤3*B.c-(8/5)*B.s-1 := by linarith only [cap,hb]
  rcases modes with first | second
  · have v := mul_nonneg ap.le (sub_nonneg.mpr vlo)
    by_cases hp : 0≤beta
    · have support := lower_pp B (-D.s) D.c
        (by dsimp [beta] at hp; nlinarith only [hp])
        (by dsimp [alpha] at ap; nlinarith only [ap])
      rw [support] at first
      have first' : D.loV+D.side≤beta*B.loU+alpha*B.loV := by
        convert first using 1 <;> dsimp [alpha,beta] <;> ring
      have u := mul_nonneg hp (sub_nonneg.mpr low.1.le)
      have margin := FullAuxWallPositiveTopMargins.c_axis_above dn bn
        (by dsimp [beta] at hp; nlinarith only [hp])
      have identity :
          beta*(B.c+(113/50)*B.s)+alpha*(3*B.c-(8/5)*B.s-1)-
            (D.c-(8/5)*D.s)=
          D.c*(2-B.c-(37/50)*B.s^2-(3/5)*B.c*B.s)+
            D.s*((3/5)-(3/5)*B.s^2+(37/50)*B.c*B.s-B.s) := by
        dsimp [alpha,beta]
        linear_combination (3*D.c-D.s)*bn.2.2
      nlinarith only [first',u,v,margin,identity,lower]
    · have hn : beta≤0 := (lt_of_not_ge hp).le
      have support := lower_np B (-D.s) D.c
        (by dsimp [beta] at hn; nlinarith only [hn])
        (by dsimp [alpha] at ap; nlinarith only [ap])
      rw [support] at first
      have first' : D.loV+D.side≤beta*(B.loU+B.side)+alpha*B.loV := by
        convert first using 1 <;> dsimp [alpha,beta] <;> ring
      have u := mul_nonpos_of_nonpos_of_nonneg hn (sub_nonneg.mpr marker.2.1.le)
      have margin := FullAuxWallPositiveTopMargins.c_axis_below dn bn
        (by dsimp [beta] at hn; nlinarith only [hn])
      have identity :
          beta*((33/20)*B.c+(47/20)*B.s)+alpha*(3*B.c-(8/5)*B.s-1)-
            (D.c-(8/5)*D.s)=
          D.c*(2-B.c-(13/20)*B.s^2+(1/20)*B.c*B.s)+
            D.s*(-(1/20)+(1/20)*B.s^2+(13/20)*B.c*B.s-B.s) := by
        dsimp [alpha,beta]
        linear_combination (3*D.c-(33/20)*D.s)*bn.2.2
      nlinarith only [first',u,v,margin,identity,lower]
  · have v := mul_pos ap (sub_pos.mpr lower)
    by_cases hp : 0≤beta
    · have support := upper_np D (-B.s) B.c
        (by dsimp [beta] at hp; nlinarith only [hp])
        (by dsimp [alpha] at ap; nlinarith only [ap])
      rw [support] at second
      have second' : (-beta)*D.loU+alpha*(D.loV+D.side)≤B.loV := by
        convert second using 1 <;> dsimp [alpha,beta] <;> ring
      have ulo : D.loU≤2*(D.c+D.s)-9/10 := by linarith only [excess,hd]
      have u := mul_nonneg hp (sub_nonneg.mpr ulo)
      have margin := FullAuxWallPositiveTopMargins.b_axis_above dn bn
        (by dsimp [beta] at hp; nlinarith only [hp])
      have identity :
          1-beta*(2*(D.c+D.s)-9/10)+alpha*(1+D.c-(8/5)*D.s)-
            (3*B.c-(8/5)*B.s)=
          1+B.c*(D.c-2+D.s^2+(2/5)*D.c*D.s-(9/10)*D.s)+
            B.s*(D.s-D.c*D.s-(2/5)*D.c^2+(9/10)*D.c) := by
        dsimp [alpha,beta]
        linear_combination (B.c-(8/5)*B.s)*dn.2.2
      nlinarith only [second',u,v,vlo,margin,identity]
    · have hn : beta≤0 := (lt_of_not_ge hp).le
      have support := upper_pp D (-B.s) B.c
        (by dsimp [beta] at hn; nlinarith only [hn])
        (by dsimp [alpha] at ap; nlinarith only [ap])
      rw [support] at second
      have second' : (-beta)*(D.loU+D.side)+alpha*(D.loV+D.side)≤B.loV := by
        convert second using 1 <;> dsimp [alpha,beta] <;> ring
      have u := mul_nonneg (neg_nonneg.mpr hn)
        (show 0≤D.loU+D.side-2*(D.c+D.s) by linarith only [center.2.1])
      have margin := FullAuxWallPositiveEndpointMargin.shallow_margin dn bn
        (by dsimp [beta] at hn; nlinarith only [hn])
      have identity :
          1-beta*(2*(D.c+D.s))+alpha*(1+D.c-(8/5)*D.s)-
            (3*B.c-(8/5)*B.s)=
          1-B.c*(1-D.c+D.c^2-(2/5)*D.c*D.s)+
            B.s*(D.s*(1-D.c)-(2/5)*D.c^2) := by
        dsimp [alpha,beta]
        linear_combination (2*B.c-(8/5)*B.s)*dn.2.2
      nlinarith only [second',u,v,vlo,margin,identity]

/-- The real paired corner and left-wall marker force these two faces
without any assumption on the opposite central angle. -/
theorem corner_marker_faces (B : OpenSquare) (bn : Normal B.c B.s)
    (hb : 1<B.side) (marker : B.Inside (33/20) (47/20))
    (high : B.Inside 1 (12/5))
    (cornerMissing : ¬B.Inside 1 3) (wallMissing : ¬B.Inside (457/500) 2) :
    B.loV+B.side≤3*B.c-B.s ∧ (457/500)*B.c+2*B.s≤B.loU := by
  have bb := normal_bounds bn
  have bc : 0<B.c := by linarith only [bb.1]
  have upperV : B.loV+B.side≤3*B.c-B.s := by
    apply le_of_not_gt
    intro bad
    apply cornerMissing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high.1,marker.2.1,marker.2.2.1,bn.1,bn.2.1,bc,bad]
  refine ⟨upperV,?_⟩
  apply le_of_not_gt
  intro bad
  apply wallMissing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [bad,marker.2.1,high.2.2.2,upperV,hb,bb.2.1,bn.1,bn.2.1,bc]

theorem faces (D B : OpenSquare)
    (dn : Normal D.c D.s) (bn : Normal B.c B.s)
    (hd : 1<D.side) (hb : 1<B.side)
    (center : D.Inside 2 2)
    (excess : D.loU+D.side-2*(D.c+D.s)<1/10)
    (bottom : D.c-(8/5)*D.s≤D.loV)
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (marker : B.Inside (33/20) (47/20))
    (modes : D.loV+D.side≤lower B (-D.s) D.c ∨ upper D (-B.s) B.c≤B.loV)
    (topMissing : ¬B.Inside (8/5) 3)
    (cornerMissing : ¬B.Inside 1 3) (wallMissing : ¬B.Inside (457/500) 2) :
    B.loU+B.side≤(8/5)*B.c+3*B.s ∧ B.loV+B.side≤3*B.c-B.s ∧
      (457/500)*B.c+2*B.s≤B.loU ∧ 3/10<B.s := by
  have bb := normal_bounds bn
  have bc : 0<B.c := by linarith only [bb.1]
  have v := endpoint_v D B dn bn hd hb center excess bottom low marker modes
  have other := corner_marker_faces B bn hb marker high cornerMissing wallMissing
  have upperU : B.loU+B.side≤(8/5)*B.c+3*B.s := by
    apply le_of_not_gt
    intro bad
    apply topMissing
    refine ⟨?_,bad,?_,?_⟩ <;>
      linarith only [high.1,marker.2.2.1,v,bc,bn.1]
  refine ⟨upperU,other.1,other.2,?_⟩
  linarith only [upperU,other.2,hb,bb.2.1]

#print axioms endpoint_v
#print axioms corner_marker_faces
#print axioms faces
end N12Compact.FullAuxWallPositiveTop
